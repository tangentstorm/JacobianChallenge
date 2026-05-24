#!/bin/bash
# script to send a message to a local gemini worker running in a tmux pane
# usage: ./msg_worker.sh <tmux_target> <message>
# example: ./msg_worker.sh 0:1.0 "Hello worker!"

TARGET=$1
shift
MESSAGE="$*"

if [ -z "$TARGET" ] || [ -z "$MESSAGE" ]; then
    echo "Usage: $0 <tmux_target> <message>"
    exit 1
fi

# Send the message text
tmux send-keys -t "$TARGET" "$MESSAGE"

# Brief delay to allow the prompt UI to register the text
sleep 0.5

# Send the Enter key
tmux send-keys -t "$TARGET" Enter

echo "Message sent to $TARGET"
