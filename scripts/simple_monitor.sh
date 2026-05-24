#!/bin/bash
# scripts/simple_monitor.sh
# Background loop to prompt the orchestrator to check worker status.

# Wait for 30 seconds between checks
INTERVAL=30
LOGFILE="/tmp/simple_monitor.log"

echo "Simple monitor started at $(date)" > "$LOGFILE"

while true; do
  TIMESTAMP=$(date "+%H:%M:%S")
  MESSAGE="[$TIMESTAMP] Simple Status Check. Monitor is alive."
  
  # Log the action
  echo "Sending message: $MESSAGE" >> "$LOGFILE"
  
  # Send to session 0, window 0 (orchestrator)
  # C-u clears the line.
  /opt/homebrew/bin/tmux send-keys -t 0:0 C-u "$MESSAGE" Enter
  
  echo "Sleeping for $INTERVAL seconds..." >> "$LOGFILE"
  sleep $INTERVAL
done
