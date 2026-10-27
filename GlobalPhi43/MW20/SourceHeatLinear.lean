module

public import GlobalPhi43.MW20.HeatFrechet
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Linearity of the actual coordinate source heat operator
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped ContDiff

/-- Addition for the actual first/second coordinate heat operator. -/
theorem sourceHeat_add (f g : ParabolicSpace → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : ParabolicSpace) :
    sourceHeat (fun z => f z + g z) x = sourceHeat f x + sourceHeat g x := by
  have hdf := (hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have hdg := (hg.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have he : fderiv ℝ (fun z => f z + g z) = fun z => fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    exact fderiv_add (hf.differentiable (by simp)).differentiableAt
      (hg.differentiable (by simp)).differentiableAt
  rw [sourceHeat_eq_fderiv_of_contDiffAt _ x ((hf.add hg).of_le (by simp)).contDiffAt,
    sourceHeat_eq_fderiv_of_contDiffAt _ x (hf.of_le (by simp)).contDiffAt,
    sourceHeat_eq_fderiv_of_contDiffAt _ x (hg.of_le (by simp)).contDiffAt,
    he]
  have hjet : fderiv ℝ (fun z => fderiv ℝ f z + fderiv ℝ g z) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    exact fderiv_add hdf.differentiableAt hdg.differentiableAt
  rw [hjet]
  simp only [add_apply, Finset.sum_add_distrib]
  ring

/-- Multiplication by a scalar, including zero and signed counterterms. -/
theorem sourceHeat_const_mul (c : ℝ) (f : ParabolicSpace → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : ParabolicSpace) :
    sourceHeat (fun z => c * f z) x = c * sourceHeat f x := by
  have hdf := (hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have he : fderiv ℝ (fun z => c * f z) = fun z => c • fderiv ℝ f z := by
    funext z
    exact fderiv_const_mul (hf.differentiable (by simp)).differentiableAt c
  rw [sourceHeat_eq_fderiv_of_contDiffAt _ x ((contDiff_const.mul hf).of_le (by simp)).contDiffAt,
    sourceHeat_eq_fderiv_of_contDiffAt _ x (hf.of_le (by simp)).contDiffAt,
    he]
  have hjet : fderiv ℝ (fun z => c • fderiv ℝ f z) x =
      c • fderiv ℝ (fderiv ℝ f) x := by
    exact fderiv_const_smul hdf.differentiableAt c
  rw [hjet]
  simp only [smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Constants are annihilated, with no differentiability premise. -/
@[simp] theorem sourceHeat_const (c : ℝ) (x : ParabolicSpace) :
    sourceHeat (fun _ => c) x = 0 := by
  have he : deriv (fun _ : ℝ => c) = fun _ => 0 := by
    funext t
    simp only [deriv_const]
  simp only [sourceHeat, he, deriv_const, Finset.sum_const_zero, sub_self]

/-- Subtracting a base-point value does not affect the source heat operator. -/
theorem sourceHeat_sub_const (f : ParabolicSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (x : ParabolicSpace) : sourceHeat (fun z => f z - c) x = sourceHeat f x := by
  simpa only [sub_eq_add_neg, sourceHeat_const, add_zero] using
    sourceHeat_add f (fun _ => -c) hf contDiff_const x

end GlobalPhi43.MW20
