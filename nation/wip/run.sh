#!/bin/bash
PYTHON_SCRIPT="main.py"
VENV_PATH="$HOME/app/latestEnv/bin/activate"
if [ -f "$PYTHON_SCRIPT" ]; then
    konsole -e bash -c "source $VENV_PATH && python3 $PYTHON_SCRIPT; exec bash"
else
    konsole -e bash -c "echo 'Error: $PYTHON_SCRIPT not found in the current directory!'; exec bash"
fi