# Git Commit and Crediting Guide

To maintain a clean, professional, and consistent repository history, all agents and automated processes must strictly adhere to the following commit and crediting conventions.

## 1. Commit Authorship and Committer

Every single commit in the repository's history must be authored and committed by the primary project developer:

*   **Name**: `Michal Wallace`
*   **Email**: `michal.wallace@gmail.com`

### Agent Git Configuration
When preparing or executing commits locally, always ensure the git configuration is set correctly:
```bash
git config user.name "Michal Wallace"
git config user.email "michal.wallace@gmail.com"
```

## 2. Co-Authorship and Agent Credits

To acknowledge contributions from AI assistants and other automated workers, use `Co-authored-by:` trailers at the **very bottom of the commit message**, separated from the body by a blank line.

### Normalized Identity Mappings

The following exact spellings and email addresses must be used for agent credits:

| Agent / Persona | Normalized Co-authored-by Trailer |
| :--- | :--- |
| **Gemini** (Antigravity, Gemini CLI, etc.) | `Co-authored-by: Gemini <gemini@google.com>` |
| **Claude** (Claude Opus, sub-agents, etc.) | `Co-authored-by: Claude <claude@anthropic.com>` |
| **Codex** (OpenAI Codex, etc.) | `Co-authored-by: Codex <codex@openai.com>` |
| **GitHub** (noreply@github.com) | `Co-authored-by: GitHub <noreply@github.com>` |
| **Aristotle** (Aristotle Lean Worker, etc.) | `Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>` |
| **Grok** (Grok xAI, etc.) | `Co-authored-by: Grok <grok@x.ai>` |

### Rules for Co-Authorship

1.  **No Redundant Self-Attribution**: The primary author (**Michal Wallace**) must **never** be listed in a `Co-authored-by:` line, as this is redundant with the commit's primary author field.
2.  **Formatting**: The trailer must be in the exact format: `Co-authored-by: Name <email>` (case-sensitive and no leading/trailing spaces around name and email).
3.  **Deterministic Ordering**: If a commit has multiple co-authors, they should be sorted alphabetically by name.
4.  **Separation**: Always leave exactly one blank line between the commit message body and the start of the `Co-authored-by:` trailer(s).

### Example Commit Message
```text
feat(ComplexTorus): prove quotientLieAddGroup_witness is sorry-free

State and prove quotientLieAddGroup_witness by showing that the translation 
action on the vector space preserves the lattice boundaries.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Gemini <gemini@google.com>
```
