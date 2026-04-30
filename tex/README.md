# Informal proof roadmap

This directory contains a standalone informal proof plan for the Jacobian
Challenge. It is intentionally separate from `blueprint/`: the goal here is to
write the classical mathematical source of truth first, then extract a
Lean-blueprint dependency graph later.

Main entrypoint:

```text
tex/main.tex
```

The document follows the analytic period-lattice construction

```text
J(X) = H^0(X, Omega^1)^dual / H_1(X, Z)
```

and mirrors the current Lean roadmap where possible. Important theorem blocks
carry `\lean{...}` annotations naming the intended Lean declaration or module.

Suggested checks:

```powershell
cd tex
latexmk -pdf main.tex
```

If no TeX distribution is installed, a useful text-only check is:

```powershell
rg "\\input|\\include" main.tex sections statements
rg "\\lean\\{" tex
```

