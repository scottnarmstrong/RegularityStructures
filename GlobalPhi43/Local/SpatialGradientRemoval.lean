/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactGradientIBP
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Sum the actual compact spatial IBP identities before returning to time. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory
open scoped ContDiff

 theorem spatial_gradient_removal {k χ h : (Fin 3 → ℝ) → ℝ}
    (hk : ContDiff ℝ ∞ k) (hχ : ContDiff ℝ ∞ χ) (hh : ContDiff ℝ ∞ h)
    (hcχ : HasCompactSupport χ) :
    (∫ z : Fin 3 → ℝ, k z * ∑ i : Fin 3, fderiv ℝ χ z (Pi.single i 1) * fderiv ℝ h z (Pi.single i 1)) =
      -(∫ z : Fin 3 → ℝ, ∑ i : Fin 3,
        (fderiv ℝ k z (Pi.single i 1) * fderiv ℝ χ z (Pi.single i 1) +
          k z * fderiv ℝ (fun w => fderiv ℝ χ w (Pi.single i 1)) z (Pi.single i 1)) * h z) := by
  let a : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i z => fderiv ℝ χ z (Pi.single i 1)
  have ha (i : Fin 3) : ContDiff ℝ ∞ (a i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hca (i : Fin 3) : HasCompactSupport (a i) := hcχ.fderiv_apply ℝ (Pi.single i 1)
  have hda (i : Fin 3) : Continuous (fun z => fderiv ℝ (a i) z (Pi.single i 1)) :=
    ((ha i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdk (i : Fin 3) : Continuous (fun z => fderiv ℝ k z (Pi.single i 1)) :=
    (hk.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdh (i : Fin 3) : Continuous (fun z => fderiv ℝ h z (Pi.single i 1)) :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiL (i : Fin 3) : Integrable (fun z => (k z * a i z) * fderiv ℝ h z (Pi.single i 1)) := by
    exact (by fun_prop : Continuous _).integrable_of_hasCompactSupport (hca i).mul_left.mul_right
  have hiR (i : Fin 3) : Integrable (fun z =>
      (fderiv ℝ k z (Pi.single i 1) * a i z + k z * fderiv ℝ (a i) z (Pi.single i 1)) * h z) := by
    exact (by fun_prop : Continuous _).integrable_of_hasCompactSupport
      (((hca i).mul_left).add (((hca i).fderiv_apply ℝ (Pi.single i 1)).mul_left)).mul_right
  have hibp (i : Fin 3) := compact_gradient_integration_by_parts
    (hk.of_le (by norm_num)) ((ha i).of_le (by norm_num)) (hh.of_le (by norm_num)) (hca i) (Pi.single i 1)
  calc
    _ = ∫ z : Fin 3 → ℝ, ∑ i : Fin 3, (k z * a i z) * fderiv ℝ h z (Pi.single i 1) := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      dsimp only [a]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin 3, ∫ z : Fin 3 → ℝ, (k z * a i z) * fderiv ℝ h z (Pi.single i 1) :=
      integral_finsetSum Finset.univ (fun i _ => hiL i)
    _ = ∑ i : Fin 3, -(∫ z : Fin 3 → ℝ,
        (fderiv ℝ k z (Pi.single i 1) * a i z + k z * fderiv ℝ (a i) z (Pi.single i 1)) * h z) :=
      Finset.sum_congr rfl (fun i _ => hibp i)
    _ = _ := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun i _ => hiR i)]

end GlobalPhi43.Local
