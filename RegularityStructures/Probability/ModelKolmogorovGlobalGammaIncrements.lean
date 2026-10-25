/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model

/-!
# Cocycle increments for the Gamma moment criterion

Deterministic identities for the Kolmogorov criterion for models [Hai14, Theorem 10.7]. The
increments in either base point follow from the cocycle property of the model. They are not
additional stochastic hypotheses. Both product-error channels are retained for a pair of models.

Source: [Hai14, Definition 2.17, first algebraic condition].
-/

public section

open MeasureTheory

namespace RegularityStructures.Model

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {Q : RegularisingSemigroup E μ}

private theorem global_gamma_apply_sum (M : Model 𝒯 Q) (x y : E) (τ : ι → ℝ) (j : ι) :
    M.gammaMap x y τ j = ∑ k, τ k * M.gammaMap x y (Pi.single k 1) j := by
  conv_lhs => rw [eq_sum_single τ]
  simp [map_sum, Finset.sum_apply]

/-- Matrix-coordinate version of the given model cocycle, with its order explicit. -/
theorem gammaMap_single_cocycle_sum
    (M : Model 𝒯 Q) (x y z : E) (i j : ι) :
    M.gammaMap x z (Pi.single i 1) j =
      ∑ k, M.gammaMap y z (Pi.single i 1) k * M.gammaMap x y (Pi.single k 1) j := by
  have he := LinearMap.congr_fun (M.gammaMap_comp x y z) (Pi.single i 1)
  change M.gammaMap x y (M.gammaMap y z (Pi.single i 1)) =
    M.gammaMap x z (Pi.single i 1) at he
  rw [← he]
  exact global_gamma_apply_sum M x y _ j

/-- Changing the left endpoint is a cocycle increment, not an assumed Holder estimate. -/
theorem gammaMap_single_left_increment
    (M : Model 𝒯 Q) (x y z : E) (i j : ι) :
    M.gammaMap z x (Pi.single i 1) j - M.gammaMap y x (Pi.single i 1) j =
      ∑ k, M.gammaMap y x (Pi.single i 1) k *
        (M.gammaMap z y (Pi.single k 1) j - (Pi.single k 1 : ι → ℝ) j) := by
  classical
  have hI : (∑ k, M.gammaMap y x (Pi.single i 1) k * (Pi.single k 1 : ι → ℝ) j) =
      M.gammaMap y x (Pi.single i 1) j := by
    simp [Pi.single_apply, mul_ite]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← M.gammaMap_single_cocycle_sum z y x i j, hI]

/-- The analogous cocycle increment in the right endpoint. -/
theorem gammaMap_single_right_increment
    (M : Model 𝒯 Q) (x y z : E) (i j : ι) :
    M.gammaMap x z (Pi.single i 1) j - M.gammaMap x y (Pi.single i 1) j =
      ∑ k, (M.gammaMap y z (Pi.single i 1) k - (Pi.single i 1 : ι → ℝ) k) *
        M.gammaMap x y (Pi.single k 1) j := by
  classical
  have hI : (∑ k, (Pi.single i 1 : ι → ℝ) k * M.gammaMap x y (Pi.single k 1) j) =
      M.gammaMap x y (Pi.single i 1) j := by
    simp [Pi.single_apply, ite_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← M.gammaMap_single_cocycle_sum x y z i j, hI]

/-- Two-model right increments, with neither error channel discarded. -/
theorem gammaMap_single_diff_right_increment
    (M Mbar : Model 𝒯 Q) (x y z : E) (i j : ι) :
    (M.gammaMap x z (Pi.single i 1) j - Mbar.gammaMap x z (Pi.single i 1) j) -
      (M.gammaMap x y (Pi.single i 1) j - Mbar.gammaMap x y (Pi.single i 1) j) =
      ∑ k,
        ((M.gammaMap y z (Pi.single i 1) k - Mbar.gammaMap y z (Pi.single i 1) k) *
          M.gammaMap x y (Pi.single k 1) j +
        (Mbar.gammaMap y z (Pi.single i 1) k - (Pi.single i 1 : ι → ℝ) k) *
          (M.gammaMap x y (Pi.single k 1) j - Mbar.gammaMap x y (Pi.single k 1) j)) := by
  have he : (∑ k,
      ((M.gammaMap y z (Pi.single i 1) k - Mbar.gammaMap y z (Pi.single i 1) k) *
        M.gammaMap x y (Pi.single k 1) j +
      (Mbar.gammaMap y z (Pi.single i 1) k - (Pi.single i 1 : ι → ℝ) k) *
        (M.gammaMap x y (Pi.single k 1) j - Mbar.gammaMap x y (Pi.single k 1) j))) =
      (∑ k, (M.gammaMap y z (Pi.single i 1) k - (Pi.single i 1 : ι → ℝ) k) *
        M.gammaMap x y (Pi.single k 1) j) -
      ∑ k, (Mbar.gammaMap y z (Pi.single i 1) k - (Pi.single i 1 : ι → ℝ) k) *
        Mbar.gammaMap x y (Pi.single k 1) j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, ← M.gammaMap_single_right_increment, ← Mbar.gammaMap_single_right_increment]
  ring

end RegularityStructures.Model

end

