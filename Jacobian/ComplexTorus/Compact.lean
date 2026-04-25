import Jacobian.ComplexTorus.Defs

/-!
# Compactness of the complex-torus quotient (re-export)

The proof of `compactSpace_quotient_of_cover` and the derived
`quotient_compactSpace` instance live in
`Jacobian/ComplexTorus/Defs.lean`, alongside the rest of the
complex-torus core. This file is kept as a thin wrapper so existing
`import Jacobian.ComplexTorus.Compact` consumers continue to work,
and as the future home for additional compactness-related helpers
on the complex-torus quotient.
-/
