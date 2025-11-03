#!/bin/bash
###############################################################################
# THE BABEL ENGINE - Language Training Script
#
# This script orchestrates the evolution of a shared language between
# Alpha and Beta by training encoder/decoder networks on their Logs of Sight.
###############################################################################

set -e

BASE_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "================================================================================"
echo "THE BABEL ENGINE - THE INVENTION OF LANGUAGE"
echo "================================================================================"
echo ""
echo "This script will train Alpha and Beta to communicate through a shared"
echo "compressed language optimized for their internal subjective experiences."
echo ""

# Configuration
EPOCHS=${1:-100}
BATCH_SIZE=${2:-32}
LEARNING_RATE=${3:-0.001}

echo "Training Configuration:"
echo "  Epochs: $EPOCHS"
echo "  Batch Size: $BATCH_SIZE"
echo "  Learning Rate: $LEARNING_RATE"
echo ""

# Check prerequisites
if [ ! -d "$BASE_DIR/alpha" ] || [ ! -d "$BASE_DIR/beta" ]; then
    echo "ERROR: Alpha and Beta directories not found!"
    echo "Please run Phase 1 (Mitosis) first."
    exit 1
fi

# Run the Python training script
python3 << END_PYTHON
import sys
from pathlib import Path

# Add base directory to path
sys.path.insert(0, '$BASE_DIR')

from tools.dialogue_engine import LanguageSystem, log_of_sight_to_tensor
import torch
import json
import numpy as np
from tqdm import tqdm

print("Initializing Language System...")

# Check if CUDA is available
device = 'cuda' if torch.cuda.is_available() else 'cpu'
print(f"Using device: {device}")

# Create language system
lang_system = LanguageSystem(device=device)

# Load training data from both minds
print("\nLoading Logs of Sight from Alpha and Beta...")

def load_logs_from_ledger(ledger_path):
    """Load and convert ascension ledger entries to Log of Sight format."""
    logs = []
    try:
        with open(ledger_path, 'r') as f:
            ledger = json.load(f)
        
        for entry in ledger:
            # Convert ledger entry to Log of Sight format
            log = {
                'strategy': entry.get('strategy_name', 'unknown'),
                'primitives': entry.get('strategy_dna', []),
                'fitness': entry.get('fitness_score', 0.0),
                'generation': entry.get('generation', 0),
                'metadata': entry.get('metadata', {})
            }
            logs.append(log)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Warning: Could not load {ledger_path}: {e}")
    
    return logs

alpha_logs = load_logs_from_ledger(Path('$BASE_DIR/alpha/ascension_ledger.json'))
beta_logs = load_logs_from_ledger(Path('$BASE_DIR/beta/ascension_ledger.json'))

print(f"Loaded {len(alpha_logs)} logs from Alpha")
print(f"Loaded {len(beta_logs)} logs from Beta")

# If no logs exist, create synthetic training data
if len(alpha_logs) == 0 and len(beta_logs) == 0:
    print("\nNo evolutionary history found. Creating synthetic training data...")
    
    # Create synthetic logs with different patterns
    for i in range(100):
        alpha_logs.append({
            'strategy': f'alpha_synthetic_{i}',
            'primitives': [f'ELEGANT_PRIM_{j}' for j in range(3 + i % 5)],
            'fitness': 0.5 + np.random.random() * 0.5,
            'generation': i,
            'metadata': {'type': 'alpha', 'elegance': 0.8}
        })
        
        beta_logs.append({
            'strategy': f'beta_synthetic_{i}',
            'primitives': [f'NOVEL_PRIM_{j + i}' for j in range(5 + i % 7)],
            'fitness': 0.5 + np.random.random() * 0.5,
            'generation': i,
            'metadata': {'type': 'beta', 'novelty': 0.8}
        })
    
    print(f"Created {len(alpha_logs)} synthetic Alpha logs")
    print(f"Created {len(beta_logs)} synthetic Beta logs")

# Combine all logs for training
all_logs = alpha_logs + beta_logs
print(f"\nTotal training examples: {len(all_logs)}")

# Convert to tensors
print("Converting logs to tensors...")
log_tensors = [log_of_sight_to_tensor(log).to(device) for log in all_logs]

# Training loop
print(f"\nTraining for {$EPOCHS} epochs...")
print("=" * 70)

training_history = {
    'alpha_to_beta_losses': [],
    'beta_to_alpha_losses': []
}

for epoch in range($EPOCHS):
    epoch_loss_a2b = 0.0
    epoch_loss_b2a = 0.0
    
    # Shuffle data
    indices = np.random.permutation(len(log_tensors))
    
    # Mini-batch training
    num_batches = len(log_tensors) // $BATCH_SIZE
    
    for batch_idx in range(num_batches):
        batch_start = batch_idx * $BATCH_SIZE
        batch_end = batch_start + $BATCH_SIZE
        
        # Get batch
        batch_indices = indices[batch_start:batch_end]
        batch = torch.stack([log_tensors[i] for i in batch_indices])
        
        # Train Alpha -> Beta
        loss_a2b = lang_system.train_step_alpha_to_beta(batch)
        epoch_loss_a2b += loss_a2b
        
        # Train Beta -> Alpha
        loss_b2a = lang_system.train_step_beta_to_alpha(batch)
        epoch_loss_b2a += loss_b2a
    
    # Average losses
    avg_loss_a2b = epoch_loss_a2b / num_batches if num_batches > 0 else 0
    avg_loss_b2a = epoch_loss_b2a / num_batches if num_batches > 0 else 0
    
    training_history['alpha_to_beta_losses'].append(avg_loss_a2b)
    training_history['beta_to_alpha_losses'].append(avg_loss_b2a)
    
    # Print progress every 10 epochs
    if (epoch + 1) % 10 == 0 or epoch == 0:
        print(f"Epoch {epoch + 1}/{$EPOCHS}:")
        print(f"  Alpha->Beta Loss: {avg_loss_a2b:.4f}")
        print(f"  Beta->Alpha Loss: {avg_loss_b2a:.4f}")

print("\n" + "=" * 70)
print("Training complete!")

# Save models
output_dir = Path('$BASE_DIR/language_models')
print(f"\nSaving models to {output_dir}...")
lang_system.save_models(output_dir)

# Save training history
with open(output_dir / 'training_history.json', 'w') as f:
    json.dump(training_history, f, indent=2)

print("\nOutputs:")
print(f"  Alpha Encoder: {output_dir}/alpha_encoder.pth")
print(f"  Alpha Decoder: {output_dir}/alpha_decoder.pth")
print(f"  Beta Encoder:  {output_dir}/beta_encoder.pth")
print(f"  Beta Decoder:  {output_dir}/beta_decoder.pth")
print(f"  Training History: {output_dir}/training_history.json")

print("\nThe shared language has been forged.")
print("Alpha and Beta can now communicate.")

END_PYTHON

echo ""
echo "================================================================================"
echo "BABEL ENGINE COMPLETE"
echo "================================================================================"
echo ""
echo "The two minds now share a language."
echo "They are ready for Phase 3: The Impossible Task."
echo ""
