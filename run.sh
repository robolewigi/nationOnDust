#!/bin/bash
PYTHON_SCRIPT="main.py"

. ~/app/latestEnv/bin/activate

if [ -f "$PYTHON_SCRIPT" ]; then
  gnome-terminal -- bash -c "python3 $PYTHON_SCRIPT; exec bash"
else
  gnome-terminal -- bash -c "python3 $PYTHON_SCRIPT; exec bash"
fi
