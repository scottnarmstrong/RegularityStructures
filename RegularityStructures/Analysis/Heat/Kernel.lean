/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Analysis.Heat.FlatExp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The heat kernel on `ℝ⁴ = ℝ × ℝ³`

`heatKernelR4 (t, x) = 1_{t>0} (4πt)^{-3/2} exp(-|x|²/(4t))`, the fundamental solution of
`∂_t - Δ`. We prove that it is nonnegative, measurable, a probability density on each time slice,
homogeneous of degree `-3` for the parabolic dilation, smooth away from the origin, and that all
its derivatives are bounded on the parabolic annulus `{1/2 ≤ ‖z‖_𝔰 ≤ 2}`.

Smoothness across `t = 0` (for `x ≠ 0`) uses the identity
`heatKernelR4 (t, x) = (4π)^{-3/2} · 8 · |x|^{-3} · flatExp (-3/2) (4t/|x|²)`.

Source: Hairer, arXiv:1303.5113v4, Assumption 5.1 and Lemma 5.5.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The heat kernel `G(t, x) = 1_{t>0} (4πt)^{-3/2} e^{-|x|²/(4t)}` on `ℝ⁴ = ℝ × ℝ³`. -/
def heatKernelR4 (z : ParabolicSpace) : ℝ := if 0 < z.1 then gaussKernel z.1 z.2 else 0

end RegularityStructures

end

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

theorem heatKernelR4_of_pos {z : ParabolicSpace} (hz : 0 < z.1) :
    heatKernelR4 z = gaussKernel z.1 z.2 := by
  simp [heatKernelR4, hz]

theorem heatKernelR4_of_nonpos {z : ParabolicSpace} (hz : z.1 ≤ 0) : heatKernelR4 z = 0 := by
  simp [heatKernelR4, not_lt.mpr hz]

theorem heatKernelR4_nonneg (z : ParabolicSpace) : 0 ≤ heatKernelR4 z := by
  by_cases hz : 0 < z.1
  · rw [heatKernelR4_of_pos hz]
    exact gaussKernel_nonneg hz _
  · rw [heatKernelR4_of_nonpos (not_lt.mp hz)]

theorem measurable_heatKernelR4 : Measurable heatKernelR4 := by
  unfold heatKernelR4 gaussKernel sqNorm3
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  fun_prop

theorem integral_heatKernelR4_slice {t : ℝ} (ht : 0 < t) :
    ∫ x : Fin 3 → ℝ, heatKernelR4 (t, x) = 1 := by
  simp only [heatKernelR4, ht, ite_true]
  exact integral_gaussKernel ht

/-! ### Homogeneity -/

theorem gaussKernel_dilate {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (x : Fin 3 → ℝ) :
    gaussKernel (c ^ 2 * t) (c • x) = (c ^ 3)⁻¹ * gaussKernel t x := by
  have hsq : sqNorm3 (c • x) = c ^ 2 * sqNorm3 x := by
    simp only [sqNorm3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hexp : -sqNorm3 (c • x) / (4 * (c ^ 2 * t)) = -sqNorm3 x / (4 * t) := by
    rw [hsq]
    field_simp
  have hpow : (4 * Real.pi * (c ^ 2 * t)) ^ (-(3 : ℝ) / 2)
      = (c ^ 3)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
    have h4 : 4 * Real.pi * (c ^ 2 * t) = c ^ 2 * (4 * Real.pi * t) := by ring
    have hp : 0 ≤ 4 * Real.pi * t := by positivity
    have hcc : (c ^ 2) ^ (-(3 : ℝ) / 2) = (c ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le, ← Real.rpow_natCast c 3,
        ← Real.rpow_neg hc.le]
      congr 1
      push_cast
      ring
    rw [h4, Real.mul_rpow (sq_nonneg c) hp, hcc]
  unfold gaussKernel
  rw [hexp, hpow]
  ring

/-- Parabolic homogeneity of degree `-3`: `G(S^c z) = c⁻³ G(z)`. -/
theorem heatKernelR4_parabolicDilate {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    heatKernelR4 (parabolicDilate c z) = (c ^ 3)⁻¹ * heatKernelR4 z := by
  by_cases hz : 0 < z.1
  · have h2 : 0 < (parabolicDilate c z).1 := by
      simp only [parabolicDilate]
      positivity
    rw [heatKernelR4_of_pos h2, heatKernelR4_of_pos hz]
    exact gaussKernel_dilate hc hz z.2
  · have h2 : (parabolicDilate c z).1 ≤ 0 := by
      simp only [parabolicDilate]
      nlinarith [sq_nonneg c, not_lt.mp hz]
    rw [heatKernelR4_of_nonpos h2, heatKernelR4_of_nonpos (not_lt.mp hz), mul_zero]

/-! ### Smoothness away from the origin -/

open scoped ContDiff

theorem contDiff_sqNorm3 : ContDiff ℝ ∞ sqNorm3 := by
  unfold sqNorm3
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

theorem four_rpow_neg_three_halves : (4 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 8 := by
  have h : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [h, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg]

theorem contDiffAt_heatKernelR4_of_pos {z : ParabolicSpace} (hz : 0 < z.1) :
    ContDiffAt ℝ ∞ heatKernelR4 z := by
  have hf : ContDiffAt ℝ ∞ (fun w : ParabolicSpace =>
      (4 * Real.pi * w.1) ^ (-(3 : ℝ) / 2) * Real.exp (-sqNorm3 w.2 / (4 * w.1))) z := by
    have h1 : ContDiffAt ℝ ∞ (fun w : ParabolicSpace => 4 * Real.pi * w.1) z :=
      contDiffAt_const.mul contDiff_fst.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ParabolicSpace => 4 * w.1) z :=
      contDiffAt_const.mul contDiff_fst.contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun w : ParabolicSpace => -sqNorm3 w.2) z :=
      (contDiff_sqNorm3.comp contDiff_snd).neg.contDiffAt
    refine (h1.rpow_const_of_ne (by positivity)).mul (h3.div h2 (by positivity)).exp
  refine hf.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
  exact heatKernelR4_of_pos hw

theorem contDiffAt_heatKernelR4_of_neg {z : ParabolicSpace} (hz : z.1 < 0) :
    ContDiffAt ℝ ∞ heatKernelR4 z := by
  refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
  exact heatKernelR4_of_nonpos (le_of_lt hw)

/-- Away from the hyperplane `x = 0`, `G` is a smooth function of `(t, x)` times a flat function
of `4t/|x|²`. -/
theorem heatKernelR4_eq_flatExp {z : ParabolicSpace} (hx : 0 < sqNorm3 z.2) :
    heatKernelR4 z = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * 8 * (sqNorm3 z.2) ^ (-(3 : ℝ) / 2) *
      flatExp (-(3 : ℝ) / 2) (4 * z.1 / sqNorm3 z.2) := by
  by_cases ht : 0 < z.1
  · have hu : 0 < 4 * z.1 / sqNorm3 z.2 := by positivity
    rw [heatKernelR4_of_pos ht, flatExp_of_pos _ hu, gaussKernel]
    have hexp : -(4 * z.1 / sqNorm3 z.2)⁻¹ = -sqNorm3 z.2 / (4 * z.1) := by
      field_simp
    rw [hexp, Real.mul_rpow (by positivity) ht.le, Real.div_rpow (by positivity) hx.le,
      Real.mul_rpow (by norm_num) ht.le, four_rpow_neg_three_halves]
    have hs : (sqNorm3 z.2) ^ (-(3 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    field_simp
  · have hu : 4 * z.1 / sqNorm3 z.2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp ht]) hx.le
    rw [heatKernelR4_of_nonpos (not_lt.mp ht), flatExp_of_nonpos _ hu, mul_zero]

theorem contDiffAt_heatKernelR4_of_time_zero {z : ParabolicSpace} (hx : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ heatKernelR4 z := by
  have hpos : 0 < sqNorm3 z.2 := by
    obtain ⟨i, hi⟩ : ∃ i, z.2 i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    unfold sqNorm3
    exact lt_of_lt_of_le (by positivity : 0 < z.2 i ^ 2) (Finset.single_le_sum
      (f := fun j => z.2 j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hU : IsOpen {w : ParabolicSpace | 0 < sqNorm3 w.2} :=
    isOpen_lt continuous_const (contDiff_sqNorm3.continuous.comp continuous_snd)
  have hs : ContDiffAt ℝ ∞ (fun w : ParabolicSpace => sqNorm3 w.2) z :=
    (contDiff_sqNorm3.comp contDiff_snd).contDiffAt
  have hf : ContDiffAt ℝ ∞ (fun w : ParabolicSpace =>
      (4 * Real.pi) ^ (-(3 : ℝ) / 2) * 8 * (sqNorm3 w.2) ^ (-(3 : ℝ) / 2) *
        flatExp (-(3 : ℝ) / 2) (4 * w.1 / sqNorm3 w.2)) z := by
    have h4 : ContDiffAt ℝ ∞ (fun w : ParabolicSpace => 4 * w.1) z :=
      contDiffAt_const.mul contDiff_fst.contDiffAt
    exact (contDiffAt_const.mul (hs.rpow_const_of_ne hpos.ne')).mul
      ((contDiff_flatExp _).contDiffAt.comp z (h4.div hs hpos.ne'))
  exact hf.congr_of_eventuallyEq (by
    filter_upwards [hU.mem_nhds hpos] with w hw
    exact heatKernelR4_eq_flatExp hw)

/-- The heat kernel is smooth away from the origin. -/
theorem contDiffAt_heatKernelR4 {z : ParabolicSpace} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ heatKernelR4 z := by
  rcases lt_trichotomy z.1 0 with h | h | h
  · exact contDiffAt_heatKernelR4_of_neg h
  · refine contDiffAt_heatKernelR4_of_time_zero fun hx => hz ?_
    exact Prod.ext h hx
  · exact contDiffAt_heatKernelR4_of_pos h

/-! ### Bounds on the annulus -/

end RegularityStructures

end
