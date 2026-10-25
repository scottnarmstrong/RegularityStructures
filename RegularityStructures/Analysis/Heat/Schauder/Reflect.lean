/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity
public import RegularityStructures.Analysis.Semigroup.Pairing.Main

/-!
# Pairing against a reflected, supported function

For a smooth `h : ℝ⁴ → ℝ` vanishing outside the parabolic ball `‖w‖_𝔰 ≤ lam`, the function
`y ↦ h (x - y)` is supported in the ball of radius `lam` about `x`, has the same `L¹` norm as `h`,
and `L (h (x - ·)) = (L h) (x - ·)` (the generator has even order).  Hence the pairing bound
`abs_pairing_le` (Hairer, arXiv:1303.5113v4, (3.3) type estimate) applies to it
(`abs_pairing_reflect_le`).
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem iteratedFDeriv_sub_left_apply {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (x y v : ParabolicSpace) :
    iteratedFDeriv ℝ k (fun y => f (x - y)) y (fun _ => v) =
      (-1 : ℝ) ^ k * iteratedFDeriv ℝ k f (x - y) (fun _ => v) := by
  set D : ParabolicSpace →L[ℝ] ParabolicSpace := -ContinuousLinearMap.id ℝ ParabolicSpace with hD
  have hk : ContDiff ℝ k f := hf.of_le (by exact_mod_cast le_top)
  have hg : ContDiff ℝ k (fun u => f (x + u)) := hk.comp (contDiff_const.add contDiff_id)
  have e : (fun y => f (x - y)) = (fun u => f (x + u)) ∘ D := by
    funext y; simp [hD, sub_eq_add_neg]
  rw [e, D.iteratedFDeriv_comp_right hg _ le_rfl, iteratedFDeriv_comp_add_left]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hD]
  have h1 : (fun _ : Fin k => (-ContinuousLinearMap.id ℝ ParabolicSpace) v) =
      fun _ => (-1 : ℝ) • v := by funext; simp
  rw [h1, (iteratedFDeriv ℝ k f (x + D y)).map_smul_univ]
  simp [hD, sub_eq_add_neg]

theorem parabolicGenerator_sub_left {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (x y : ParabolicSpace) :
    parabolicGenerator (fun y => f (x - y)) y = parabolicGenerator f (x - y) := by
  unfold parabolicGenerator
  simp only [iteratedFDeriv_sub_left_apply hf, ← Finset.mul_sum]
  norm_num

/-- If `h` vanishes outside the closed ball of radius `lam` then so does `L h`. -/
theorem parabolicGenerator_eq_zero_of_lt {h : ParabolicSpace → ℝ} {lam : ℝ}
    (hh : ∀ w, lam < parabolicNorm w → h w = 0) {w : ParabolicSpace}
    (hw : lam < parabolicNorm w) : parabolicGenerator h w = 0 := by
  have hU : IsOpen {u : ParabolicSpace | lam < parabolicNorm u} :=
    isOpen_lt continuous_const continuous_parabolicNorm
  have hev : h =ᶠ[nhds w] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hw) hh
  have h1 : ∀ n, iteratedFDeriv ℝ n h w = iteratedFDeriv ℝ n (fun _ : ParabolicSpace => (0 : ℝ)) w :=
    fun n => (hev.iteratedFDeriv ℝ n).self_of_nhds
  have h0 : ∀ n, iteratedFDeriv ℝ n (fun _ : ParabolicSpace => (0 : ℝ)) w = 0 := fun n => by
    rw [iteratedFDeriv_fun_zero]
    rfl
  unfold parabolicGenerator
  rw [h1 2, h1 4, h0 2, h0 4]
  simp

theorem integral_abs_sub_left (h : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    ∫ y, |h (x - y)| = ∫ w, |h w| := by
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
    have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
    infer_instance
  exact integral_sub_left_eq_self (fun w => |h w|) volume x

end RegularityStructures

end
