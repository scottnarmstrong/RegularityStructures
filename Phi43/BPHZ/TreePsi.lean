/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiField
public import Phi43.BPHZ.TreePsiMoment

/-!
# The tree `Ψ` ([Hai14, p. 166])

Facade for the results on `Ψ(z) = ∫ K(z - w) ξ_ε(w) dw`:

* `hairerPsiField_ae_eq`: `Ψ(z) = W (K_ε(z - ·))` almost surely (stochastic Fubini);
* `hairerPsiField_integral_mul`: `E[Ψ(z) Ψ(z')] = Q_ε(z - z')`;
* `measurable_hairerPsiField_uncurry`: `(ω, z) ↦ Ψ(ω, z)` is jointly measurable.
-/
