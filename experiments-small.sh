#!/bin/bash
# experiments-small: Run small experiment grid for Thiele Machine

cd "$(dirname "$0")"

python run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 14 --seed-grid 0 1 2 --repeat 1 --emit-receipts