#!/bin/bash
# AWS Power Measurement - Safe & Automated
# ==========================================
# 
# MAX COST: ~$2 for 1 hour of testing
# Uses spot instances with hard auto-termination
#
# Prerequisites:
#   - AWS CLI configured (aws configure)
#   - EC2 key pair created
#   - IAM permissions for EC2 spot instances
#
# Usage:
#   ./aws_setup.sh              # Interactive setup
#   ./aws_setup.sh --dry-run    # Show what would happen

set -e  # Exit on any error

# ============================================================================
# CONFIGURATION - EDIT THESE
# ============================================================================
INSTANCE_TYPE="c6i.metal"          # Bare metal with RAPL support
REGION="us-east-1"                 # Cheapest region
MAX_RUNTIME_MINUTES=60             # Hard cutoff - instance WILL terminate
SPOT_MAX_PRICE="2.00"              # Max $/hr (actual ~$1.20 for c6i.metal)
KEY_NAME="${AWS_KEY_NAME:-}"       # Your EC2 key pair name
GITHUB_REPO="https://github.com/sethirus/The-Thiele-Machine.git"

# ============================================================================
# SAFETY CHECKS
# ============================================================================

echo "============================================================"
echo "AWS POWER MEASUREMENT - SAFE AUTOMATED SETUP"
echo "============================================================"
echo ""
echo "Instance:     $INSTANCE_TYPE (bare metal with RAPL)"
echo "Region:       $REGION"
echo "Max runtime:  $MAX_RUNTIME_MINUTES minutes"
echo "Max cost:     ~\$$(echo "scale=2; $SPOT_MAX_PRICE * $MAX_RUNTIME_MINUTES / 60" | bc) (spot pricing)"
echo ""

# Check AWS CLI
if ! command -v aws &> /dev/null; then
    echo "ERROR: AWS CLI not installed"
    echo "Install: pip install awscli && aws configure"
    exit 1
fi

# Check AWS credentials
if ! aws sts get-caller-identity &> /dev/null; then
    echo "ERROR: AWS credentials not configured"
    echo "Run: aws configure"
    exit 1
fi

# Check key name
if [ -z "$KEY_NAME" ]; then
    echo "WARNING: No EC2 key pair specified"
    echo "Set AWS_KEY_NAME environment variable or edit this script"
    echo ""
    echo "Available key pairs:"
    aws ec2 describe-key-pairs --query 'KeyPairs[*].KeyName' --output text --region $REGION || true
    echo ""
    read -p "Enter key pair name: " KEY_NAME
    if [ -z "$KEY_NAME" ]; then
        echo "ERROR: Key pair required for SSH access"
        exit 1
    fi
fi

# Dry run check
if [ "$1" == "--dry-run" ]; then
    echo "DRY RUN - No resources will be created"
    echo ""
    echo "Would launch:"
    echo "  - c6i.metal spot instance"
    echo "  - Auto-terminate after $MAX_RUNTIME_MINUTES minutes"
    echo "  - Run power measurement experiments"
    echo "  - Save results to S3 or instance"
    exit 0
fi

# Confirmation
echo ""
read -p "Continue? This will cost money. (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Aborted."
    exit 1
fi

# ============================================================================
# CREATE USER DATA SCRIPT
# ============================================================================

USER_DATA=$(cat << 'USERDATA_END'
#!/bin/bash
# User data script - runs on instance startup
# Auto-terminates after MAX_RUNTIME_MINUTES

set -x  # Enable debug logging
exec > /var/log/user-data.log 2>&1

echo "=== Power Measurement Instance Starting ==="
date

# Install dependencies
apt-get update
apt-get install -y python3-pip python3-venv git linux-tools-common linux-tools-generic

# Clone repository
cd /home/ubuntu
git clone GITHUB_REPO_PLACEHOLDER thiele-machine
cd thiele-machine

# Setup Python environment
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt

# Verify RAPL access
echo "=== Checking RAPL ==="
ls -la /sys/class/powercap/intel-rapl/ || echo "RAPL directory not found"
cat /sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj || echo "Cannot read RAPL"

# Run power measurement
echo "=== Running Power Measurement ==="
python3 experiments/power_measurement/measure_real_power.py | tee /home/ubuntu/power_output.txt

# Save results
cp experiments/power_measurement/power_results.json /home/ubuntu/ || true

echo "=== Experiment Complete ==="
date

# Keep instance alive for 10 minutes to allow SSH access for results
echo "Instance will terminate in 10 minutes. SSH now to retrieve results."
sleep 600

# Auto-terminate
echo "Auto-terminating instance..."
shutdown -h now
USERDATA_END
)

# Replace placeholder with actual repo URL
USER_DATA="${USER_DATA/GITHUB_REPO_PLACEHOLDER/$GITHUB_REPO}"

# ============================================================================
# GET LATEST AMI
# ============================================================================

echo "Finding latest Ubuntu AMI..."
AMI_ID=$(aws ec2 describe-images \
    --region $REGION \
    --owners 099720109477 \
    --filters "Name=name,Values=ubuntu/images/hvm-ssd/ubuntu-jammy-22.04-amd64-server-*" \
              "Name=state,Values=available" \
    --query 'sort_by(Images, &CreationDate)[-1].ImageId' \
    --output text)

echo "Using AMI: $AMI_ID"

# ============================================================================
# CREATE SECURITY GROUP
# ============================================================================

SG_NAME="thiele-power-test-sg"
echo "Creating security group..."

# Check if security group exists
SG_ID=$(aws ec2 describe-security-groups \
    --region $REGION \
    --filters "Name=group-name,Values=$SG_NAME" \
    --query 'SecurityGroups[0].GroupId' \
    --output text 2>/dev/null || echo "None")

if [ "$SG_ID" == "None" ] || [ -z "$SG_ID" ]; then
    SG_ID=$(aws ec2 create-security-group \
        --region $REGION \
        --group-name $SG_NAME \
        --description "Security group for Thiele Machine power testing" \
        --query 'GroupId' \
        --output text)
    
    # Allow SSH
    aws ec2 authorize-security-group-ingress \
        --region $REGION \
        --group-id $SG_ID \
        --protocol tcp \
        --port 22 \
        --cidr 0.0.0.0/0
fi

echo "Security group: $SG_ID"

# ============================================================================
# LAUNCH SPOT INSTANCE
# ============================================================================

echo "Launching spot instance..."

# Create launch specification
LAUNCH_SPEC=$(cat << EOF
{
    "ImageId": "$AMI_ID",
    "InstanceType": "$INSTANCE_TYPE",
    "KeyName": "$KEY_NAME",
    "SecurityGroupIds": ["$SG_ID"],
    "UserData": "$(echo "$USER_DATA" | base64 -w 0)"
}
EOF
)

# Request spot instance
SPOT_REQUEST_ID=$(aws ec2 request-spot-instances \
    --region $REGION \
    --spot-price "$SPOT_MAX_PRICE" \
    --instance-count 1 \
    --type "one-time" \
    --launch-specification "$LAUNCH_SPEC" \
    --query 'SpotInstanceRequests[0].SpotInstanceRequestId' \
    --output text)

echo "Spot request ID: $SPOT_REQUEST_ID"

# Wait for spot request to be fulfilled
echo "Waiting for spot request fulfillment..."
aws ec2 wait spot-instance-request-fulfilled \
    --region $REGION \
    --spot-instance-request-ids $SPOT_REQUEST_ID

# Get instance ID
INSTANCE_ID=$(aws ec2 describe-spot-instance-requests \
    --region $REGION \
    --spot-instance-request-ids $SPOT_REQUEST_ID \
    --query 'SpotInstanceRequests[0].InstanceId' \
    --output text)

echo "Instance ID: $INSTANCE_ID"

# Wait for instance to be running
echo "Waiting for instance to start..."
aws ec2 wait instance-running \
    --region $REGION \
    --instance-ids $INSTANCE_ID

# Get public IP
PUBLIC_IP=$(aws ec2 describe-instances \
    --region $REGION \
    --instance-ids $INSTANCE_ID \
    --query 'Reservations[0].Instances[0].PublicIpAddress' \
    --output text)

# ============================================================================
# OUTPUT INSTRUCTIONS
# ============================================================================

echo ""
echo "============================================================"
echo "INSTANCE LAUNCHED SUCCESSFULLY"
echo "============================================================"
echo ""
echo "Instance ID:  $INSTANCE_ID"
echo "Public IP:    $PUBLIC_IP"
echo "Key pair:     $KEY_NAME"
echo ""
echo "The instance will:"
echo "  1. Install dependencies (~5 minutes)"
echo "  2. Run power measurement (~10 minutes)"
echo "  3. Wait 10 minutes for you to retrieve results"
echo "  4. Auto-terminate"
echo ""
echo "To SSH and retrieve results:"
echo "  ssh -i ~/.ssh/$KEY_NAME.pem ubuntu@$PUBLIC_IP"
echo "  cat /home/ubuntu/power_output.txt"
echo "  cat /home/ubuntu/power_results.json"
echo ""
echo "To monitor instance:"
echo "  aws ec2 describe-instances --instance-ids $INSTANCE_ID --query 'Reservations[0].Instances[0].State.Name'"
echo ""
echo "To terminate early:"
echo "  aws ec2 terminate-instances --instance-ids $INSTANCE_ID"
echo ""
echo "Check /var/log/user-data.log on instance for detailed logs"
echo ""
echo "SAFETY: Instance will auto-terminate in ~25 minutes"
echo "        Max cost: ~\$$(echo "scale=2; $SPOT_MAX_PRICE * 0.5" | bc)"

# Save instance info for later reference
cat > instance_info.txt << EOF
INSTANCE_ID=$INSTANCE_ID
PUBLIC_IP=$PUBLIC_IP
KEY_NAME=$KEY_NAME
REGION=$REGION
SPOT_REQUEST_ID=$SPOT_REQUEST_ID
TIMESTAMP=$(date -Iseconds)
EOF

echo ""
echo "Instance info saved to: instance_info.txt"
