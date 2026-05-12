# Tmux & AI Agent Interaction Guide

When interacting with AI agents (Codex, Gemini, Claude) running in a `tmux` session via `tmux send-keys`, follow these timing and formatting rules to ensure reliable execution.

## 1. The "Pause-before-Enter" Rule
AI agents often use "paste detection" logic. If a prompt and the final newline are sent in a single rapid burst, the agent may simply append a blank line to the buffer instead of executing the command.
- **Protocol:**
  1. Send the command/prompt string.
  2. **Pause for at least 1 second.**
  3. Send the final `Enter` key.

## 2. Clearing the Buffer
Before sending a new prompt, ensure the command line is clean to avoid "command-stuffing."
- **Protocol:** Send `C-c` (Control-C) followed by an `Enter` before starting a new prompt string.

## 3. Handling Multi-line Prompts
When sending complex multi-line instructions:
- Ensure the entire prompt is enclosed in appropriate quotes (usually single quotes `'...'` for bash/zsh).
- If the agent is within its own specialized CLI (e.g., the `gemini >` prompt), ensure the quotes match that environment's expectations.

## 4. Verification Pattern
Always verify that the agent has transitioned to the "Thinking" or "Working" state after submission.
- **Check:** `tmux capture-pane -pt <session>:<window>.<pane>`
- **Expected:** Output should show "Thinking..." or a progress bar, not just the prompt text sitting at the bottom of the screen.
