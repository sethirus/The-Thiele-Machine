#!/bin/bash
# Real-time Coq compilation monitor with memory and status tracking

TARGET="${1:-thielemachine/verification/BridgeDefinitions.vo}"
LOG_FILE="/tmp/coq_build_$(date +%s).log"

echo "=========================================="
echo "COQ BUILD MONITOR"
echo "Target: $TARGET"
echo "Started: $(date)"
echo "Log: $LOG_FILE"
echo "=========================================="
echo ""

# Monitor memory in background
monitor_memory() {
    while true; do
        if pgrep -f "coqc.*BridgeDefinitions" > /dev/null; then
            MEM=$(ps aux | grep -E "coqc.*BridgeDefinitions" | grep -v grep | awk '{print $6}')
            if [ -n "$MEM" ]; then
                MEM_MB=$((MEM / 1024))
                CPU=$(ps aux | grep -E "coqc.*BridgeDefinitions" | grep -v grep | awk '{print $3}')
                echo -ne "\r[$(date +%H:%M:%S)] Memory: ${MEM_MB}MB | CPU: ${CPU}%        "
            fi
        fi
        sleep 0.5
    done
}

# Start memory monitor in background
monitor_memory &
MONITOR_PID=$!

# Run the build with output
cd /workspaces/The-Thiele-Machine/coq
make "$TARGET" 2>&1 | tee "$LOG_FILE" | while IFS= read -r line; do
    echo "$line"
    # Highlight important lines
    if echo "$line" | grep -q "COQC"; then
        echo -e "\n==> COMPILING: $(echo $line | sed 's/.*COQC //')"
    elif echo "$line" | grep -q "Error"; then
        echo -e "\n❌ ERROR DETECTED ❌"
    elif echo "$line" | grep -q "File.*line"; then
        echo -e "📍 $(echo $line | grep -o 'File.*line [0-9]*')"
    fi
done

BUILD_EXIT=$?

# Kill memory monitor
kill $MONITOR_PID 2>/dev/null
echo -e "\n"

echo "=========================================="
echo "BUILD FINISHED: $(date)"
echo "Exit code: $BUILD_EXIT"
echo "Log saved to: $LOG_FILE"

# Show summary
if [ $BUILD_EXIT -eq 0 ]; then
    echo "✅ SUCCESS"
else
    echo "❌ FAILED"
    echo ""
    echo "=== LAST ERROR ==="
    grep -A 5 "Error:" "$LOG_FILE" | tail -20
fi
echo "=========================================="

exit $BUILD_EXIT
