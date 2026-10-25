/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.Compat

/-!
# Polynomial compatibility: injectivity and `Γ` on polynomials

Aggregator for `RegularityStructures.Abstract.Integration.PolyCompat`: the approximate identity for
functions of polynomial growth (`Approx`, `ApproxPoly`), injectivity of `τ ↦ (Q_t (· - x)^τ)_{t>0}`
(`polyReg_injective`, `Inject`), and for `M.IsPolyCompatible P` the injectivity of `Π_x` on
`P.subspace` and the formula for `Γ_{xy} X^k` (`Compat`). Input to [Hai14, Lemma 5.16].
-/
