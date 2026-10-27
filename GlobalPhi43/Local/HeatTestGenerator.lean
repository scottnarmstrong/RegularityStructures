/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GaussianJointHeat
public import GlobalPhi43.Local.SpatialSliceSecond

/-! The ordinary backward heat generator on compact space-time tests. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory
open scoped ContDiff

/-- Time derivative plus spatial Laplacian; its negative is the adjoint of
sourceHeat. This is an explicit differential expression. -/
def heatTestGenerator (φ : ParabolicSpace → ℝ) (p : ParabolicSpace) : ℝ :=
  fderiv ℝ φ p (1, 0) + ∑ i : Fin 3,
    fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ φ q (0, Pi.single i 1)) p (0, Pi.single i 1)

 theorem heatTestGenerator_contDiff {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (heatTestGenerator φ) := by
  have hfirst : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (1, 0)) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hsecond (i : Fin 3) : ContDiff ℝ ∞ (fun p =>
      fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ φ q (0, Pi.single i 1)) p (0, Pi.single i 1)) :=
    by
      have hg : ContDiff ℝ ∞ (fun q : ParabolicSpace => fderiv ℝ φ q (0, Pi.single i 1)) :=
        (hφ.fderiv_right (by simp)).clm_apply contDiff_const
      exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact hfirst.add (ContDiff.sum fun i _ => hsecond i)

 theorem heatTestGenerator_hasCompactSupport {φ : ParabolicSpace → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (heatTestGenerator φ) := by
  have htime := hφ.fderiv_apply ℝ ((1, 0) : ParabolicSpace)
  have hs (i : Fin 3) := (hφ.fderiv_apply ℝ ((0, Pi.single i 1) : ParabolicSpace)).fderiv_apply
    ℝ ((0, Pi.single i 1) : ParabolicSpace)
  have hsum := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hs i)
  exact htime.add hsum

 theorem hasDerivAt_gaussian_heat_generator {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcomp : HasCompactSupport φ) {t : ℝ} (ht : 0 < t)
    (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => ∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (s, y - Real.sqrt s • z))
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * heatTestGenerator φ (t, y - Real.sqrt t • z)) t := by
  have hh := hasDerivAt_gaussian_joint_heat hφ hcomp ht y
  convert hh using 1
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  congr 1
  unfold heatTestGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (spatial_slice_second_apply hφ t (y - Real.sqrt t • z) (Pi.single i 1) (Pi.single i 1)).symm

end GlobalPhi43.Local
