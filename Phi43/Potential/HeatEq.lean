/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelCalc
public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.PDE.GaussDeriv

/-!
# The heat equation for the Euclidean heat kernel `heatKernelR4`

For `t > 0` the kernel `G(t, x) = (4πt)^{-3/2} e^{-|x|²/(4t)}` of `ℝ × ℝ³` solves
`(∂_t - Δ) G = 0` (`heatEq_heatKernelR4`), in the form
`ddv 0 G z - ∑ j, ddv j.succ (ddv j.succ G) z = 0` of the global derivatives `ddv` of
`Phi43.Inhomogeneity`.  The proof writes `G = exp ∘ L` with `L = -(3/2) log(4πt) - |x|²/(4t)` and
computes the first and second derivatives of `L` along the coordinate lines.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Potential

/-- The exponent `L(t, x) = -(3/2) log (4πt) - |x|²/(4t)` of the heat kernel. -/
def potLogHeat (z : ParabolicSpace) : ℝ :=
  -(3 / 2) * Real.log (4 * Real.pi * z.1) - sqNorm3 z.2 / (4 * z.1)

end RegularityStructures.Potential

end

public section

open Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity RegularityStructures.Datum

/-- The derivative of `F` in the direction `stBasis j` is the derivative along the coordinate
line. -/
theorem ddv_eq_of_hasDerivAt_line {F : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hF : DifferentiableAt ℝ F z) (j : Fin 4) {d : ℝ}
    (h : HasDerivAt (fun r : ℝ => F (z + r • stBasis j)) d 0) : ddv j F z = d := by
  have hline : HasDerivAt (fun r : ℝ => z + r • stBasis j) (stBasis j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (stBasis j)).const_add z
  have h1 := (by simpa using hF : DifferentiableAt ℝ F (z + (0 : ℝ) • stBasis j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline
  simp only [zero_smul, add_zero] at h1
  exact h1.unique h

theorem line_time (z : ParabolicSpace) (r : ℝ) : z + r • stBasis 0 = (z.1 + r, z.2) := by
  rw [stBasis_zero]; ext <;> simp

theorem line_space (z : ParabolicSpace) (j : Fin 3) (r : ℝ) :
    z + r • stBasis j.succ = (z.1, z.2 + r • Pi.single j 1) := by
  rw [stBasis_succ]; ext <;> simp

theorem differentiableAt_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) :
    DifferentiableAt ℝ potLogHeat z := by
  unfold potLogHeat sqNorm3
  have h1 : (4 * Real.pi * z.1) ≠ 0 := by positivity
  have h2 : (4 * z.1) ≠ 0 := by positivity
  fun_prop (disch := assumption)

theorem ddv_zero_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) :
    ddv 0 potLogHeat z = -3 / (2 * z.1) + sqNorm3 z.2 / (4 * z.1 ^ 2) := by
  refine ddv_eq_of_hasDerivAt_line (differentiableAt_potLogHeat hz) 0 ?_
  have e : (fun r : ℝ => potLogHeat (z + r • stBasis 0)) = fun r =>
      -(3 / 2) * Real.log (4 * Real.pi * (z.1 + r)) - sqNorm3 z.2 / (4 * (z.1 + r)) := by
    funext r; rw [line_time]; rfl
  rw [e]
  have h1 : HasDerivAt (fun r : ℝ => 4 * Real.pi * (z.1 + r)) (4 * Real.pi) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add z.1).const_mul (4 * Real.pi)
  have h2 : HasDerivAt (fun r : ℝ => 4 * (z.1 + r)) 4 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add z.1).const_mul 4
  have hp : (4 * Real.pi * (z.1 + 0)) ≠ 0 := by simp; positivity
  have hq : (4 * (z.1 + 0)) ≠ 0 := by simp; positivity
  have := ((h1.log hp).const_mul (-(3 / 2))).sub ((hasDerivAt_const (0 : ℝ) (sqNorm3 z.2)).div h2 hq)
  convert this using 1
  have : z.1 ≠ 0 := hz.ne'
  field_simp
  ring

theorem ddv_succ_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) (j : Fin 3) :
    ddv j.succ potLogHeat z = -z.2 j / (2 * z.1) := by
  refine ddv_eq_of_hasDerivAt_line (differentiableAt_potLogHeat hz) j.succ ?_
  have e : (fun r : ℝ => potLogHeat (z + r • stBasis j.succ)) = fun r =>
      -(3 / 2) * Real.log (4 * Real.pi * z.1) - (sqNorm3 z.2 + 2 * r * z.2 j + r ^ 2) / (4 * z.1) := by
    funext r; rw [line_space, potLogHeat, PDE.sqNorm3_add_smul_single]
  rw [e]
  have hq : (4 * z.1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => sqNorm3 z.2 + 2 * r * z.2 j + r ^ 2) (2 * z.2 j) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (2 * z.2 j)).add
      ((hasDerivAt_id (0 : ℝ)).pow 2)).const_add (sqNorm3 z.2)
    convert this using 1
    · funext r; simp; ring
    · simp
  have := (hasDerivAt_const (0 : ℝ) (-(3 / 2) * Real.log (4 * Real.pi * z.1))).sub
    (h1.div_const (4 * z.1))
  convert this using 1
  have : z.1 ≠ 0 := hz.ne'
  field_simp
  ring

theorem differentiableAt_ddv_succ_potLogHeat_aux {z : ParabolicSpace} (hz : 0 < z.1) (j : Fin 3) :
    DifferentiableAt ℝ (fun w : ParabolicSpace => -w.2 j / (2 * w.1)) z := by
  have : (2 * z.1) ≠ 0 := by positivity
  fun_prop (disch := assumption)

theorem ddv_succ_succ_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) (j : Fin 3) :
    ddv j.succ (ddv j.succ potLogHeat) z = -1 / (2 * z.1) := by
  have hev : ddv j.succ potLogHeat =ᶠ[𝓝 z] fun w : ParabolicSpace => -w.2 j / (2 * w.1) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
    exact ddv_succ_potLogHeat hw j
  have : ddv j.succ (ddv j.succ potLogHeat) z =
      ddv j.succ (fun w : ParabolicSpace => -w.2 j / (2 * w.1)) z := by
    simp only [ddv, hev.fderiv_eq]
  rw [this]
  refine ddv_eq_of_hasDerivAt_line (differentiableAt_ddv_succ_potLogHeat_aux hz j) j.succ ?_
  have e : (fun r : ℝ => (fun w : ParabolicSpace => -w.2 j / (2 * w.1)) (z + r • stBasis j.succ)) =
      fun r => -(z.2 j + r) / (2 * z.1) := by
    funext r; rw [line_space]; simp
  rw [e]
  have hq : (2 * z.1) ≠ 0 := by positivity
  have := (((hasDerivAt_id (0 : ℝ)).const_add (z.2 j)).neg).div_const (2 * z.1)
  simpa using this

theorem gaussKernel_eq_exp_potLogHeat {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    gaussKernel t y = Real.exp (potLogHeat (t, y)) := by
  have h : 0 < 4 * Real.pi * t := by positivity
  rw [gaussKernel, Real.rpow_def_of_pos h, ← Real.exp_add, potLogHeat]
  congr 1
  ring

theorem ddv_exp {F : ParabolicSpace → ℝ} {z : ParabolicSpace} (hF : DifferentiableAt ℝ F z)
    (j : Fin 4) :
    ddv j (fun w => Real.exp (F w)) z = Real.exp (F z) * ddv j F z := by
  simp only [ddv, fderiv_exp hF]
  simp

theorem differentiableAt_exp_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) :
    DifferentiableAt ℝ (fun w => Real.exp (potLogHeat w)) z :=
  (differentiableAt_potLogHeat hz).exp

theorem ddv_succ_exp_potLogHeat_ev {z : ParabolicSpace} (hz : 0 < z.1) (j : Fin 3) :
    ddv j.succ (fun w => Real.exp (potLogHeat w)) =ᶠ[𝓝 z]
      fun w : ParabolicSpace => Real.exp (potLogHeat w) * (-w.2 j / (2 * w.1)) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
  rw [ddv_exp (differentiableAt_potLogHeat hw), ddv_succ_potLogHeat hw]

theorem ddv_succ_succ_exp_potLogHeat {z : ParabolicSpace} (hz : 0 < z.1) (j : Fin 3) :
    ddv j.succ (ddv j.succ (fun w => Real.exp (potLogHeat w))) z =
      Real.exp (potLogHeat z) * ((-z.2 j / (2 * z.1)) ^ 2 + -1 / (2 * z.1)) := by
  have h1 : ddv j.succ (ddv j.succ (fun w => Real.exp (potLogHeat w))) z =
      ddv j.succ (fun w : ParabolicSpace => Real.exp (potLogHeat w) * (-w.2 j / (2 * w.1))) z := by
    simp only [ddv, (ddv_succ_exp_potLogHeat_ev hz j).fderiv_eq]
  rw [h1]
  have hd := differentiableAt_ddv_succ_potLogHeat_aux hz j
  have h2 : ddv j.succ (fun w : ParabolicSpace => Real.exp (potLogHeat w) * (-w.2 j / (2 * w.1))) z =
      Real.exp (potLogHeat z) * ddv j.succ (fun w : ParabolicSpace => -w.2 j / (2 * w.1)) z +
        (-z.2 j / (2 * z.1)) * ddv j.succ (fun w => Real.exp (potLogHeat w)) z := by
    simp only [ddv]
    rw [fderiv_fun_mul (differentiableAt_exp_potLogHeat hz) hd]
    simp
  have h3 : ddv j.succ (fun w : ParabolicSpace => -w.2 j / (2 * w.1)) z = -1 / (2 * z.1) := by
    have := ddv_succ_succ_potLogHeat hz j
    have hev : ddv j.succ potLogHeat =ᶠ[𝓝 z] fun w : ParabolicSpace => -w.2 j / (2 * w.1) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
      exact ddv_succ_potLogHeat hw j
    rw [← this]
    simp only [ddv, hev.fderiv_eq]
  rw [h2, h3, ddv_exp (differentiableAt_potLogHeat hz), ddv_succ_potLogHeat hz]
  ring

theorem heatKernelR4_eventuallyEq {z : ParabolicSpace} (hz : 0 < z.1) :
    heatKernelR4 =ᶠ[𝓝 z] fun w => Real.exp (potLogHeat w) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
  rw [heatKernelR4_of_pos hw, gaussKernel_eq_exp_potLogHeat hw]

/-- **The heat equation** `(∂_t - Δ) G = 0` for the heat kernel `G = heatKernelR4` on `{t > 0}`. -/
theorem heatEq_heatKernelR4 {z : ParabolicSpace} (hz : 0 < z.1) :
    ddv 0 heatKernelR4 z - ∑ j : Fin 3, ddv j.succ (ddv j.succ heatKernelR4) z = 0 := by
  have hev := heatKernelR4_eventuallyEq hz
  have hev2 : ∀ j : Fin 3, ddv j.succ heatKernelR4 =ᶠ[𝓝 z]
      ddv j.succ (fun w => Real.exp (potLogHeat w)) := by
    intro j
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
    have := (heatKernelR4_eventuallyEq hw)
    simp only [ddv, this.fderiv_eq]
  have e0 : ddv 0 heatKernelR4 z = ddv 0 (fun w => Real.exp (potLogHeat w)) z := by
    simp only [ddv, hev.fderiv_eq]
  have e1 : ∀ j : Fin 3, ddv j.succ (ddv j.succ heatKernelR4) z =
      ddv j.succ (ddv j.succ (fun w => Real.exp (potLogHeat w))) z := by
    intro j
    simp only [ddv, (hev2 j).fderiv_eq]
  rw [e0, Finset.sum_congr rfl fun j _ => e1 j, ddv_exp (differentiableAt_potLogHeat hz),
    ddv_zero_potLogHeat hz]
  simp only [ddv_succ_succ_exp_potLogHeat hz, ← Finset.mul_sum]
  have h2 : (0 : ℝ) < 2 * z.1 := by positivity
  have hs : sqNorm3 z.2 = ∑ j : Fin 3, z.2 j ^ 2 := rfl
  have hz0 : z.1 ≠ 0 := hz.ne'
  have : ∑ j : Fin 3, ((-z.2 j / (2 * z.1)) ^ 2 + -1 / (2 * z.1)) =
      sqNorm3 z.2 / (4 * z.1 ^ 2) - 3 / (2 * z.1) := by
    rw [Finset.sum_add_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_div]
    have hsq : ∀ j : Fin 3, (-z.2 j / (2 * z.1)) ^ 2 = z.2 j ^ 2 / (4 * z.1 ^ 2) := by
      intro j; field_simp; ring
    simp only [hsq]
    ring
  rw [this]
  ring

end RegularityStructures.Potential

end
