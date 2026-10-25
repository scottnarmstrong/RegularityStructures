/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Realising
public import RegularityStructures.Abstract.Singular.TwoModel.Bounds
public import RegularityStructures.Abstract.Singular.TwoModel.Gamma

/-!
# The difference model satisfies the hypotheses of the extension bounds

For two models `M₁, M₂` realising the kernel with profile `h` for `I` on `V`, the difference model
`M⊕ = modelSum` (`Π⊕_x (a, b) = λ⁻¹ (Π¹_x − Π²_x) a + Π²_x b`) on the structure `𝒯⊕ = structSumU P`
with `V⊕`, `I⊕`, `P⊕` satisfies `Model.ExtSetting` with the constants `max C_{Π₂} (λ⁻¹ C_{dΠ})`
and `max (max C_{Γ₁} C_{Γ₂}) (λ⁻¹ C_{dΓ})` (`Model.extSetting_modelSum`).  The single-model bounds
for `M⊕` are the two-model bounds [Hai14, (5.18), second line].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

/-- If `0 ≤ B` and `X ≤ A + ε B` for all `ε > 0`, then `X ≤ A`. -/
theorem le_of_forall_pos_le_add_mul {X A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ A + ε * B) : X ≤ A := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 := h (δ / (B + 1)) (by positivity)
  have h2 : δ / (B + 1) * B ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end RegularityStructures

end
