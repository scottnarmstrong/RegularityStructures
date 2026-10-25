/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decay.Poly
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Iterated derivatives of the heat kernel on `{t > 0}`

For every list `L` of directions there is a polynomial expression `P` in `t⁻¹, x` with
`lineIter L heatKernelR4 z = P z * heatKernelR4 z` for `t > 0` (`exists_lineIter_heatKernelR4`).
The key step is the logarithmic derivative `D_d G = g_d G` with
`g_d = -(3/2) d₀ t⁻¹ - (1/2) t⁻¹ ⟨x, d'⟩ + (1/4) d₀ t⁻² |x|²` (`exists_dirDeriv_heatKernelR4`).
-/

public section

open scoped ContDiff

namespace RegularityStructures

private theorem fderiv_sqNorm3_snd (z : ParabolicSpace) :
    HasFDerivAt (fun w : ParabolicSpace => sqNorm3 w.2)
      (∑ i : Fin 3, (2 * z.2 i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))) z := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasFDerivAt (fun w : ParabolicSpace => w.2 i ^ 2)
        ((2 * z.2 i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))) z := by
    intro i _
    have h1 : HasFDerivAt (fun w : ParabolicSpace => w.2 i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) z :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z
        (hasFDerivAt_snd (𝕜 := ℝ) (p := z)))
    simpa using h1.pow 2
  simpa [sqNorm3] using HasFDerivAt.fun_sum h

/-- The logarithm of the heat kernel on `{t > 0}`. -/
private noncomputable def logHeat (w : ParabolicSpace) : ℝ :=
  Real.log (4 * Real.pi * w.1) * (-(3 : ℝ) / 2) + (-sqNorm3 w.2) * (4 * w.1)⁻¹

private theorem heatKernelR4_eq_exp_logHeat {w : ParabolicSpace} (hw : 0 < w.1) :
    heatKernelR4 w = Real.exp (logHeat w) := by
  rw [heatKernelR4_of_pos hw, gaussKernel, logHeat, Real.exp_add,
    Real.rpow_def_of_pos (by positivity), div_eq_mul_inv (-sqNorm3 w.2)]

private theorem dirDeriv_logHeat {z : ParabolicSpace} (hz : 0 < z.1) (d : ParabolicSpace) :
    ∃ L : ParabolicSpace →L[ℝ] ℝ, HasFDerivAt logHeat L z ∧
      L d = -(3 / 2) * d.1 * z.1⁻¹ - (1 / 2) * z.1⁻¹ * ∑ i, z.2 i * d.2 i +
        (1 / 4) * d.1 * (z.1⁻¹ * z.1⁻¹) * sqNorm3 z.2 := by
  have ht : HasFDerivAt (fun w : ParabolicSpace => w.1) (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) z :=
    hasFDerivAt_fst
  have h4 := ht.const_mul 4
  have hinv := (hasDerivAt_inv (by positivity : 4 * z.1 ≠ 0)).comp_hasFDerivAt z h4
  have hlog := (ht.const_mul (4 * Real.pi)).log (by positivity)
  have h := (hlog.mul_const (-(3 : ℝ) / 2)).add ((fderiv_sqNorm3_snd z).neg.mul hinv)
  refine ⟨_, h, ?_⟩
  have e : ∑ x, 2 * z.2 x * d.2 x = 2 * ∑ x, z.2 x * d.2 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp
  field_simp
  rw [e]
  ring

/-- The logarithmic derivative of the heat kernel is a polynomial in `t⁻¹, x`. -/
theorem exists_dirDeriv_heatKernelR4 (d : ParabolicSpace) :
    ∃ g, IsGaussPoly g ∧
      ∀ z : ParabolicSpace, 0 < z.1 → dirDeriv d heatKernelR4 z = g z * heatKernelR4 z := by
  refine ⟨fun z => ((-(3 / 2) * d.1) * z.1⁻¹ + ((-(1 / 2)) * z.1⁻¹) * ∑ i, z.2 i * d.2 i) +
    ((1 / 4) * d.1) * (z.1⁻¹ * z.1⁻¹) * ∑ i, z.2 i * z.2 i, ?_, fun z hz => ?_⟩
  · refine (((IsGaussPoly.const _).mul IsGaussPoly.invT).add (((IsGaussPoly.const _).mul
      IsGaussPoly.invT).mul (IsGaussPoly.sum fun i _ => (IsGaussPoly.coord i).mul
        (IsGaussPoly.const _)))).add (((IsGaussPoly.const _).mul
      (IsGaussPoly.invT.mul IsGaussPoly.invT)).mul
        (IsGaussPoly.sum fun i _ => (IsGaussPoly.coord i).mul (IsGaussPoly.coord i)))
  · obtain ⟨L, hL, hLd⟩ := dirDeriv_logHeat hz d
    have h := hL.exp.congr_of_eventuallyEq (f₁ := heatKernelR4) (by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
      exact heatKernelR4_eq_exp_logHeat hw)
    simp only [dirDeriv, h.fderiv, smul_apply, smul_eq_mul, hLd]
    rw [← heatKernelR4_eq_exp_logHeat hz]
    simp only [sqNorm3, sq]
    ring

/-- Every iterated derivative of the heat kernel is a polynomial in `t⁻¹, x` times the kernel
on `{t > 0}`. -/
theorem exists_lineIter_heatKernelR4 (L : List ParabolicSpace) :
    ∃ P, IsGaussPoly P ∧
      ∀ z : ParabolicSpace, 0 < z.1 → lineIter L heatKernelR4 z = P z * heatKernelR4 z := by
  induction L with
  | nil => exact ⟨fun _ => 1, IsGaussPoly.const 1, fun z _ => by simp⟩
  | cons d L ih =>
    obtain ⟨P, hP, hPz⟩ := ih
    obtain ⟨g, hg, hgz⟩ := exists_dirDeriv_heatKernelR4 d
    obtain ⟨p, hp, hpz⟩ := hP.exists_dirDeriv d
    refine ⟨fun z => P z * g z + p z, (hP.mul hg).add hp, fun z hz => ?_⟩
    have hev : lineIter L heatKernelR4 =ᶠ[nhds z] fun w => P w * heatKernelR4 w := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
      exact hPz w hw
    have h1 := (hP.contDiffAt hz).differentiableAt (by simp)
    have h2 := (contDiffAt_heatKernelR4_of_pos hz).differentiableAt (by simp)
    have hpz' := hpz z hz
    have hgz' := hgz z hz
    simp only [dirDeriv] at hpz' hgz'
    simp only [lineIter_cons, dirDeriv, hev.fderiv_eq]
    rw [fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hpz', hgz']
    ring

end RegularityStructures

end
