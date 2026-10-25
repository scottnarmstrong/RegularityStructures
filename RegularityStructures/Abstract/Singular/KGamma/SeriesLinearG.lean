/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesLinear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.KGamma.SeriesRadius2G

/-!
# The Taylor kernel: linearity of the model pairing, weighted models

Weighted (`_growth`) version of `Model.pairing_regPi_dTaylor_eq_sum` of
`RegularityStructures.Abstract.Singular.KGamma.SeriesLinear` (the lemmas on `⌈σ⌉` are model-free and
reused): `⟨Π_x τ, K^{k,σ}_{n;yx}⟩ = ∑_i τ_i ⟨Π_x e_i, K^{k,σ}_{n;yx}⟩` for all scales `n ≥ 0`.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

/-- Linearity in `τ` of `⟨Π_x τ, K^{k,σ}_{n;yx}⟩`, all scales (weighted models). -/
theorem pairing_regPi_dTaylor_eq_sum_growth (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ}
    (hσ : 0 < σ) (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ}
    {ρP ρG : ParabolicSpace → ℝ} (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {x y : ParabolicSpace} (n : ℕ) (hd : 0 < parabolicNorm (y - x))
    (hdn : parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹) :
    parabolicSemigroup.pairing (M.regPi x τ) (dTaylorKernel h k n σ x y) =
      ∑ i, τ i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (dTaylorKernel h k n σ x y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨Cd, hCd, H⟩ := exists_dTaylor_zero_data hh k hσ
    have hd1 : parabolicNorm (y - x) ≤ 1 := by simpa using hdn
    obtain ⟨hcd, hsupp, hder⟩ := H x y hd hd1
    have hE : 0 < Cd * parabolicNorm (y - x) ^ σ := by positivity
    exact M.pairing_regPi_eq_sum_single_of_deriv_bound_growth G hdeg hτ hE hcd hsupp hder
  · obtain ⟨C, hC, H⟩ := exists_isScaledTest_dTaylorKernel hh k hσ
    exact M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg hτ (H n hn x y hd hdn)

end Model

end RegularityStructures

end
