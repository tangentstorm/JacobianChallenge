# Cloud Workers Guide

This guide documents the protocol for working with Claude Code cloud workers in the browser via Playwright and interacting with local auxiliary workers (like `jc1` running in tmux). This is a living document and should be continuously updated as new workflows or constraints are discovered.

## Initial Setup & Playwright Access

1. **Browser Server:** The MCP Playwright server manages the browser instance. Playwright typically runs headlessly in the background.
2. **Foreground Viewing:** If the user requests to see the browser window on their local desktop (e.g., macOS), use:
   `osascript -e 'tell application "Google Chrome" to activate'`
   This script forces the background Chrome window to the foreground so the user can see what's happening.

## Protocol for Talking to Cloud Workers (Claude / Aristotle)

1. **Assigning Tasks:**
   - Source assignments from the project database (e.g., `sorries.jsonl`).
   - **Difficulty Routing:** Assign harder, structurally complex issues to **Claude**, and route easier, isolated, or smaller issues to **Aristotle**.
   - **Aristotle Limits:** You MUST ensure that **EXACTLY 15 Aristotle jobs** are in-flight or in the queue at all times. Continuously refill the queue to maintain this count.
   - **Anti-Cheating Standards:** Instruct workers strictly to maintain high anti-cheating standards. They must *never* change foundational definitions, trivialize mathematical objects, or delete high-integrity scaffolding (like `ULift` wrappers) to artificially pass theorems.
   - **Prompt Quality:** Ensure all prompts strictly follow the established `ref/prompting-guide.md`. The initial prompt MUST explicitly instruct Claude to rename its own session to match the Job ID prefix (e.g., "Please rename this session to '1469. Prove skeletal homology quotient identity'").
   - **Existing Prompts:** Before generating new prompts for an assignment, *always* check the `prompts/` directory to see if an unprocessed prompt already exists for that task, and dispatch it first.
   
2. **Session Management (Claude):**
   - **Concurrency Limit:** The orchestrator must aim to **keep around 10 Claude workers busy**. If the number of active/blocked sessions exceeds 10, **do not spawn new sessions** until the total count of active tasks drops below 10. As soon as one Claude worker successfully finishes its task (merges its PR), the session should be unpinned. If the count drops below 10, the orchestrator must immediately pick the next available prompt from the `prompts/` directory and dispatch it to a fresh Claude session.
   - **Environment Selection:** When creating a new session, you MUST ensure that the environment is set to `lean`. Open the environment dropdown (which typically says "Default") and select the `lean` environment. This ensures the cloud worker has the necessary tools to compile and test the code.
   - **Naming Convention:** Whenever a new session is started, it must be renamed to place the **sorry ID number in front** (e.g., `1469. Prove skeletal homology quotient identity`). This is crucial for tracking. The best way to achieve this is to tell Claude to name its own session in the initial prompt.
   - **Renaming Protocol (Fallback):** If Claude fails to rename its own session, the most reliable way to rename a session in the Playwright/Claude UI manually is to **double-click** the session name in the sidebar. Do not rely on the "More options" dropdown menu as it is brittle.
   - **Reusing Blocked Sessions:** A session is **NOT COMPLETE** just because it reported a blocker. If a worker reports a blocker, **do not close or unpin the session**. It remains active and counts towards the 10-worker limit. Once the orchestrator or local workers have pushed the upstream fixes to `main`, return to that exact session, instruct the worker to `git pull origin main`, and have it resume its work.
   - **Single-Use Sessions (Completed Tasks):** A session is ONLY considered complete when its working proof is manually merged into `main` by the orchestrator (or if it was spawned in the wrong environment). Only then should you **unpin the session** and start a brand new one for the next task.

3. **Execution Workflow:**
   - Cloud workers are fully responsible for doing the actual implementation work and submitting it by **opening a pull request**.
   - **Monitoring & Coaching:** The orchestrator agent must check on the workers by reading their chats. If a worker encounters build errors, test failures, or gets their PR rejected, chat with them in their specific session window to correct their course.
   - **Mandatory Review:** The orchestrator **MUST manually review** every Claude session once it claims to be done (whether it opened a PR or reported a blocker). Read the chat history to verify the outcome.
   - **Unblocking:** If a worker reports that a task is BLOCKED (e.g., due to missing upstream infrastructure, incorrect definitions, or typeclass errors), the orchestrator must actively unblock it. The orchestrator should **delegate the code investigation and prompt generation** for the fix to a local worker (like `jc1`). However, **if there is no local worker available to unblock the task, the orchestrator should give the blocked Claude worker the task of unblocking itself** (e.g., by asking it to come up with a proposal, modify upstream definitions, or write the missing infrastructure).
   - **Mandatory CI Wait:** The orchestrator **MUST wait for GitHub Actions CI to clear** (turn green) before merging any PR. The orchestrator should monitor the Claude UI directly for the CI status indicator (e.g., waiting for the CI icon to turn green) rather than asking the worker to check it.
   - **Handling CI Failures:** If the CI checks fail (indicated by a red/failed status in the Claude UI or GitHub), the orchestrator MUST instruct the Claude worker to investigate the logs and push a fix.
   - **Merging:** The orchestrator **MUST merge the PRs manually** (via `git merge` or GitHub UI). Do NOT instruct the cloud worker to merge its own changes. ONLY merge if you have actually reviewed the code via `git diff`, verified they didn't cheat, AND the GitHub Actions CI is fully green. When manually merging, **you MUST credit the author with a `Co-authored-by:` line** in the commit message (e.g., `Co-authored-by: Claude <noreply@anthropic.com>`).

## Local Auxiliary Workers (`jc1`, `jc2`)

- **Role Separation:** 
  - **`jc1`:** Dedicated to assigning and managing Aristotle jobs, syncing the Aristotle ledger/dashboard, and **investigating blockers to write/fix prompts**.
  - **`jc2`:** Dedicated to making upstream structural fixes, repairing definitions, and building infrastructure to unblock the Claude workers. *(Note: Claude cloud workers are highly capable and can also be assigned these integration/fix tasks if local workers are busy).*
- **Orchestrator Freedom:** This separation of concerns ensures that the main Gemini CLI session (the orchestrator) remains fast and free to poll workers, review completed Claude PRs, manage Playwright sessions, and respond interactively to the user's questions.

## Automation Tools

A library of JavaScript commands for interacting with the Claude UI is maintained in `scripts/claude-tools.js`. 
- Use the Playwright `browser_run_code_unsafe` tool to inject these snippets when interacting with the Claude UI. 
- Avoid relying on brittle CSS selectors (like `[ref=e123]`); instead, use the library functions to locate editable inputs, type messages, press Enter, and navigate sessions robustly.gate sessions robustly.