/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTheorem
public import RegularityStructures.Abstract.Model

/-!
# Truncation `Q_{<γ}` on `D^{γ',η'}_P`, and Theorem 7.8 with Hairer's exponent conditions

The integration operator of [Hai14, Theorem 7.1] maps `D^{γ̄,η̄}_P` into `D^{γ̄+β, η_K}_P` with
`η_K = (η̄ ∧ ζ̄) + β`, and Theorem 7.8 uses it, after the projection `Q⁻_γ = Q_{<γ}`, in `D^{γ,η}_P`
under the conditions `γ < γ̄ + β` and `η < η_K`.

* `Model.SingularBoundOn.lowerProj`: for `γ ≤ γ'`, `f ∈ D^{γ',η'}_P` on `S` gives
  `Q_{<γ} f ∈ D^{γ, η' ∧ γ}_P` on `S` with `|||Q_{<γ} f||| ≤ (1 + |ι| C_Γ) |||f|||`, `C_Γ` a bound
  for `Γ` on `S` ([Hai14, §3, truncation of modelled distributions], weighted form);
* `Model.exists_unique_slab_fixedPoint_of_integration` (**Theorems 7.1 and 7.8 with Hairer's
  conditions**): if `𝒦 = Q_{<γ} 𝒦₀` on the slab, where `𝒦₀ g ∈ D^{γ_K,η_K}_P` on the slab with the
  vanishing bound of order `η_K` and constant `C |||g|||` (`C` uniform in `T`: the bounds
  established in the proof of Theorem 7.1), `γ ≤ γ_K`, `η < η_K`, `η < γ`, and the slab satisfies
  `ρ ≤ T^{1/𝔰₀}`, then the fixed-point theorem holds with the gain
  `θ = ((η_K ∧ γ) − η)/𝔰₀ > 0`.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.1, Theorem 7.8.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `(Γ τ)_j = ∑_i τ_i (Γ e_i)_j`. -/
theorem gammaMap_apply_eq_sum (x y : E) (τ : ι → ℝ) (j : ι) :
    M.gammaMap y x τ j = ∑ i, τ i * M.gammaMap y x (Pi.single i 1) j := by
  conv_lhs => rw [eq_sum_single τ]
  simp [map_sum, map_smul, Finset.sum_apply]

end Model

end RegularityStructures

end
