/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514.SumSetting

/-!
# The two-model bound for `Π` on the integrated symbols `I e_i`

[Hai14, Theorem 5.14, (5.18), second line], `Π` part: for two models `M₁, M₂` realising the
kernel with profile `h` for `I` on `V`, `e_i ∈ V`, `deg i < γ`,
`|(Q_t Π¹_x I e_i)(x) − (Q_t Π²_x I e_i)(x)| ≤ c (C_{dΠ} G + C_{Π₂} C_{dΓ}) t^{(deg i + 2)/4}`
with `G = max (max C_{Γ₁} C_{Γ₂}) 1` (`Model.exists_abs_regPi_integral_sub_le`).

The proof applies the single-model bound `exists_abs_regPi_integral_le_in` to the difference model
`M⊕` (`RegularityStructures.Abstract.Ext514.SumSetting`) with `λ ≈ C_{dΓ}/G`, whose `Π`-part on
`I⊕ e_{inl i}` is `λ⁻¹ (Π¹ − Π²) I e_i`, and lets `λ` approach `C_{dΓ}/G`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

/-- The index `i` is a polynomial index: `I e_i = 0`, so every difference vanishes. -/
theorem integral_single_eq_zero_of_mem_range {P : PolynomialSector 𝒯 N'}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hI : IsAbstractIntegration P V I 2) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hip : i ∈ Set.range P.emb) :
    I (Pi.single i 1) = 0 := by
  obtain ⟨k, rfl⟩ := hip
  exact hI.map_poly _ hVi (single_emb_mem_subspace P k)

end Model

end RegularityStructures

end
