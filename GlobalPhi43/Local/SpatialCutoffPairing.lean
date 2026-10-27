/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialGradientRemoval

/-! Combine compact spatial IBP with the exact cutoff-source algebra. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory
open scoped ContDiff

 theorem spatial_cutoff_pairing {k χ h b : (Fin 3 → ℝ) → ℝ}
    (hk : ContDiff ℝ ∞ k) (hχ : ContDiff ℝ ∞ χ) (hh : ContDiff ℝ ∞ h)
    (hb : ContDiff ℝ ∞ b) (hcχ : HasCompactSupport χ) (hcb : HasCompactSupport b) :
    Integrable (fun z : Fin 3 → ℝ => k z * (h z * b z - 2 * ∑ i : Fin 3,
      fderiv ℝ χ z (Pi.single i 1) * fderiv ℝ h z (Pi.single i 1))) ∧
    (∫ z : Fin 3 → ℝ, k z * (h z * b z - 2 * ∑ i : Fin 3,
      fderiv ℝ χ z (Pi.single i 1) * fderiv ℝ h z (Pi.single i 1))) =
      ∫ z : Fin 3 → ℝ, (k z * (b z + 2 * ∑ i : Fin 3,
        fderiv ℝ (fun w => fderiv ℝ χ w (Pi.single i 1)) z (Pi.single i 1)) +
          2 * ∑ i : Fin 3, fderiv ℝ k z (Pi.single i 1) * fderiv ℝ χ z (Pi.single i 1)) * h z := by
  let a : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i z => fderiv ℝ χ z (Pi.single i 1)
  let d : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i z => fderiv ℝ (a i) z (Pi.single i 1)
  let B : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i z =>
    (fderiv ℝ k z (Pi.single i 1) * a i z + k z * d i z) * h z
  have ha (i : Fin 3) : ContDiff ℝ ∞ (a i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hca (i : Fin 3) : HasCompactSupport (a i) := hcχ.fderiv_apply ℝ (Pi.single i 1)
  have hd (i : Fin 3) : ContDiff ℝ ∞ (d i) :=
    ((ha i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcd (i : Fin 3) : HasCompactSupport (d i) := (hca i).fderiv_apply ℝ (Pi.single i 1)
  have hdk (i : Fin 3) : Continuous (fun z => fderiv ℝ k z (Pi.single i 1)) :=
    (hk.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdh (i : Fin 3) : Continuous (fun z => fderiv ℝ h z (Pi.single i 1)) :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiA : Integrable (fun z => k z * h z * b z) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport hcb.mul_left
  have hiB (i : Fin 3) : Integrable (B i) :=
    (by dsimp [B]; fun_prop : Continuous (B i)).integrable_of_hasCompactSupport
      (((hca i).mul_left).add (hcd i).mul_left).mul_right
  have hiJ (i : Fin 3) : Integrable (fun z => (k z * a i z) * fderiv ℝ h z (Pi.single i 1)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (hca i).mul_left.mul_right
  have heJ : (fun z => k z * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1)) =
      (fun z => ∑ i : Fin 3, (k z * a i z) * fderiv ℝ h z (Pi.single i 1)) := by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hJint : Integrable (fun z => k z * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1)) := by
    rw [heJ]
    exact integrable_finsetSum Finset.univ (fun i _ => hiJ i)
  have hBint : Integrable (fun z => ∑ i : Fin 3, B i z) :=
    integrable_finsetSum Finset.univ (fun i _ => hiB i)
  have hIBP := spatial_gradient_removal hk hχ hh hcχ
  have hsum (z : Fin 3 → ℝ) : (∑ i : Fin 3, B i z) =
      (∑ i : Fin 3, fderiv ℝ k z (Pi.single i 1) * a i z) * h z +
        k z * (∑ i : Fin 3, d i z) * h z := by
    dsimp only [B]
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have heL : (fun z => k z * (h z * b z - 2 * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1))) =
      (fun z => k z * h z * b z - 2 * (k z * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1))) := by
    funext z
    ring
  have heR : (fun z => (k z * (b z + 2 * ∑ i : Fin 3, d i z) +
      2 * ∑ i : Fin 3, fderiv ℝ k z (Pi.single i 1) * a i z) * h z) =
      (fun z => k z * h z * b z + 2 * ∑ i : Fin 3, B i z) := by
    funext z
    rw [hsum]
    ring
  constructor
  · rw [heL]
    exact hiA.sub (hJint.const_mul 2)
  · change (∫ z : Fin 3 → ℝ, k z * (h z * b z - 2 * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1))) = _
    rw [heL, integral_sub hiA (hJint.const_mul 2), integral_const_mul]
    change (∫ z : Fin 3 → ℝ, k z * h z * b z) -
      2 * (∫ z : Fin 3 → ℝ, k z * ∑ i : Fin 3, a i z * fderiv ℝ h z (Pi.single i 1)) =
        ∫ z : Fin 3 → ℝ, (k z * (b z + 2 * ∑ i : Fin 3, d i z) +
          2 * ∑ i : Fin 3, fderiv ℝ k z (Pi.single i 1) * a i z) * h z
    rw [heR, integral_add hiA (hBint.const_mul 2), integral_const_mul, hIBP]
    ring


end GlobalPhi43.Local
