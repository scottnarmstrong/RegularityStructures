/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.MeasPairing
public import RegularityStructures.Abstract.Model

/-!
# Measurability of `x ↦ 𝒦_γ f(x)`

Under `Model.IsJointMeasurable` (joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)`), the
coefficients `x ↦ jCoeff M N x i k` (for `deg i < γ`, `|k|_𝔰 < deg i + 2`) and
`x ↦ nCoeff M N f x k` (for `|k|_𝔰 < γ + 2`) are measurable, and so is `x ↦ 𝒦_γ f(x)`
(`Model.measurable_kGamma`).  The coefficients with `deg i ≥ γ` are multiplied by `f(x)_i = 0`.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 5.12 (measurability is part of `D^{γ+2}`).
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)` for each `i` and `t > 0`. -/
def Model.IsJointMeasurable (M : Model 𝒯 parabolicSemigroup) : Prop :=
  ∀ i, ∀ t : ℝ, 0 < t → Measurable fun p : ParabolicSpace × ParabolicSpace =>
    M.regPi p.1 (Pi.single i 1) t p.2

end RegularityStructures

end

