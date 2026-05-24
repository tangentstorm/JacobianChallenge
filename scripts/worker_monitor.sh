#!/bin/bash
# scripts/worker_monitor.sh
# Background loop to prompt the orchestrator to check worker status.

INTERVAL=600 # 10 minutes
LOGFILE="worker_monitor.log"

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Monitor starting at $(date) using msg_worker.sh" > "$LOGFILE"

while true; do
  TIMESTAMP=$(date "+%H:%M:%S")
  
  # Log the action
  echo "Sending status prompt at $TIMESTAMP" >> "$LOGFILE"
  
  # Call the reliable msg_worker.sh script with the exact command 'status'
  "$DIR/msg_worker.sh" 0:0 "status"
  
  sleep $INTERVAL
done
