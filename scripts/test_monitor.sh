#!/bin/bash
INTERVAL=10
LOGFILE="simple_monitor.log"
echo "Monitor started at $(date)" > "$LOGFILE"
while true; do
  echo "Ping $(date)" >> "$LOGFILE"
  /opt/homebrew/bin/tmux send-keys -t 0:0 C-u "ping" Enter
  sleep $INTERVAL
done
