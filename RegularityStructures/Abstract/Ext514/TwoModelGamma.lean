/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514.TwoModelPi
public import RegularityStructures.Abstract.Model

/-!
# The two-model bound for `Γ` on the integrated symbols `I e_i`

[Hai14, Theorem 5.14, (5.18), second line], `Γ` part: for two models `M₁, M₂` realising the
kernel with profile `h` for `I` on `V`, `e_i ∈ V`, `deg i < γ`, and `deg j < deg i + 2`,
`|((Γ¹_{yx} − Γ²_{yx}) I e_i)_j| ≤ c (C_{dΠ} G² + C_{dΓ} (C_I + C_{Π₂} G)) d(y,x)^{deg i + 2 − deg j}`,
`G = max (max C_{Γ₁} C_{Γ₂}) 1` (`Model.exists_abs_gammaMap_integral_sub_le`).

As for `Π`, the proof applies the single-model bound `exists_abs_gammaMap_integral_le` to the
difference model, whose block `Γ⊕_{yx} I⊕ e_{inl i}` in the `inr` component is
`λ⁻¹ (Γ¹_{yx} − Γ²_{yx}) I e_i`, with `λ ≈ C_{dΓ}/G`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace TwoModel

variable {P : PolynomialSector 𝒯 N'}

theorem extendNP_restrictNP_of_poly_zero {w : ι → ℝ} (hw : ∀ k : PolyIndex N', w (P.emb k) = 0) :
    extendNP P (restrictNP P w) = w := by
  funext i
  by_cases hk : i ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hk
    rw [extendNP_apply_of_mem P _ ⟨k, rfl⟩, hw k]
  · rw [extendNP_apply_of_notMem P _ hk]
    rfl

end TwoModel

end RegularityStructures

end
