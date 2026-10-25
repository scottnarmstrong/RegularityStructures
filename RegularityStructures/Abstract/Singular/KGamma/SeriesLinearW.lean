/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesLinearG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# The Taylor kernel: linearity of the model pairing, window models

Window (`_win`) version of `Model.pairing_regPi_dTaylor_eq_sum_growth` of
`RegularityStructures.Abstract.Singular.KGamma.SeriesLinearG`:
`⟨Π_x τ, K^{k,σ}_{n;yx}⟩ = ∑_i τ_i ⟨Π_x e_i, K^{k,σ}_{n;yx}⟩` for all scales `n ≥ 0`. This is an
identity: the qualitative growth model enters only through the existence of the pairings, and no
constant is involved.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

/-- Linearity in `τ` of `⟨Π_x τ, K^{k,σ}_{n;yx}⟩`, all scales (window models). -/
theorem pairing_regPi_dTaylor_eq_sum_win (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ}
    (hσ : 0 < σ) (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {x y : ParabolicSpace} (n : ℕ) (hd : 0 < parabolicNorm (y - x))
    (hdn : parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹) :
    parabolicSemigroup.pairing (M.regPi x τ) (dTaylorKernel h k n σ x y) =
      ∑ i, τ i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (dTaylorKernel h k n σ x y) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.pairing_regPi_dTaylor_eq_sum_growth hh k hσ G hdeg hτ n hd hdn

end Model

end RegularityStructures

end
