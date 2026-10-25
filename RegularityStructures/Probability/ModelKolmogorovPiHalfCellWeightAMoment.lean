/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightARand
public import RegularityStructures.Probability.ModelKolmogorovPiHalfWeightedFamily

/-!
# The moment of the random part of the cell weight (A2)

`exists_piHalfCellRandPartA_moment_le`: for `s ∈ (0, 1]`, `2 p ≤ q`,
`∫⁻ ω, R(ω)^p ≤ (K max(1,C) C s^((deg k + κbar)/4))^p`, where
`R = ∫⁻ w, E^n_s(x₀ - w) R'_k(w)`.  The pointwise moment of `R'_k(·, w)` comes from
`piHalf_term_pointwise_moment` and Minkowski for the envelope integral from
`exists_kernelBlockEnvelope_weightedFamily_lintegral_pow_moment_le`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The combined `s`-exponent `β_j + α_j / 4` of a random summand is at least `(deg k + κbar)/4`. -/
theorem piHalf_rand_exponent_ge {𝒯 : RegularityStructure ι} {κbar : ℝ} (hκ : 0 < κbar)
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {k j : ι}
    (hj : ¬ (j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ))) :
    (𝒯.deg k + κbar) / 4 ≤
      piHalfRandBetaA 𝒯 κbar Dπ j + piHalfRandAlphaA 𝒯 κbar DΓ k j / 4 := by
  classical
  unfold piHalfRandBetaA piHalfRandAlphaA
  by_cases hP : j ∈ Dπ <;> by_cases hG : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ
  · exact absurd ⟨hP, hG⟩ hj
  · simp only [hP, hG, ite_true, ite_false]; linarith
  · simp only [hP, hG, ite_true, ite_false]; linarith
  · simp only [hP, hG, ite_false]; linarith

theorem piHalf_rand_alpha_bounds {𝒯 : RegularityStructure ι} {κbar : ℝ} (hκ : 0 < κbar)
    {DΓ : Set (ι × ι)} {k j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) :
    0 ≤ piHalfRandAlphaA 𝒯 κbar DΓ k j ∧
      piHalfRandAlphaA 𝒯 κbar DΓ k j ≤ 𝒯.deg k - 𝒯.deg j + κbar := by
  classical
  unfold piHalfRandAlphaA
  split_ifs <;> constructor <;> linarith

end RegularityStructures

end
