/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialLinearRepresentation

/-! Finite-coordinate bounds for the source's spatial derivative operators. -/
public noncomputable section

namespace GlobalPhi43.Local

open scoped BigOperators

theorem spatial_operator_norm_le_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin 3 → ℝ) →L[ℝ] F) : ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have he : L v = ∑ i, v i • L (Pi.single i 1) := by
    calc
      L v = L (∑ i, Pi.single i (v i)) := congrArg L (Finset.univ_sum_single v).symm
      _ = ∑ i, L (Pi.single i (v i)) := by rw [map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle : (Pi.single i (v i) : Fin 3 → ℝ) = v i • Pi.single i 1 := by
          ext j
          by_cases h : j = i <;> simp [h]
        rw [hsingle, map_smul]
  rw [he, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
    (norm_nonneg _)

theorem spatial_hessian_norm_le_sum
    (H : (Fin 3 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ)) :
    ‖H‖ ≤ ∑ i, ∑ j, |H (Pi.single i 1) (Pi.single j 1)| := by
  apply (spatial_operator_norm_le_sum H).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs] using spatial_operator_norm_le_sum (H (Pi.single i 1))

end GlobalPhi43.Local
