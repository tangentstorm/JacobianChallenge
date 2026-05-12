#!/bin/bash
# Periodic heartbeat for jc0 orchestrator
# Sends a status check to the main pane every 10 minutes

while true; do
  sleep 600
  # Send to session 0, window 0 (the orchestrator)
  # Using C-u first to clear any partial input in the prompt
  tmux send-keys -t 0:0 C-u "status?" Enter
done
