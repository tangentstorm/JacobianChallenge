# Pushing Guide for Accepted Worker Changes

This guide applies only after the manager has reviewed a worker result and decided to **ACCEPT** the changes. It is not part of normal proof development.

The purpose of this phase is to make an accepted branch merge-ready without mixing proof work, rebasing, and generated `sorries.jsonl` churn into ordinary proving tasks.

## 1. Preconditions

Do not start this workflow unless the manager has explicitly said the work is accepted.

Before pushing or merging, confirm:

- the accepted Lean changes are committed;
- `result.md` accurately describes the accepted work;
- `.swarm-status` starts with `READY:` and is under 50 characters;
- there are no unrelated scratch files staged for commit.

## 2. Rebase Onto Main

After ACCEPT, rebase the accepted branch onto the latest `origin/main`:

```bash
git fetch origin main
git rebase origin/main
```

If the rebase creates nontrivial conflicts in core Lean files or `sorries.jsonl`, stop and report the conflict to the manager. Do not force a questionable merge.

## 3. Full Verification

After the rebase, run the full project verification:

```bash
lake exe cache get
lake build Jacobian.Solution
```

The build must succeed. Warnings of the form `declaration uses sorry` are expected while the project still has open sorries. New non-sorry warnings are not acceptable.

## 4. Update sorries.jsonl Last

Only after the rebased branch builds, update the sorry database:

```bash
python3 scripts/fix-sorries.py
python3 scripts/audit-sorries.py sorries.jsonl
```

`sorries.jsonl` should be the last generated project file updated before merge. Do not manually edit it.

If `audit-sorries.py` fails, stop and report the failure. Do not merge.

## 5. Final Commit

If `fix-sorries.py` changed `sorries.jsonl`, commit that change separately or in the final merge-prep commit, according to the manager's instructions.

Before pushing, check:

```bash
git status --short
git diff --check
```

Only intentional Lean changes, accepted documentation changes, and the final `sorries.jsonl` update should be present.

## 6. Push

Push only after the accepted branch is rebased, builds, and has an audited `sorries.jsonl`:

```bash
git push
```

If the push is rejected because the remote moved, stop and ask the manager whether to rebase again or force-push.
