/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothCharacters
public import RegularityStructures.Analysis.Heat.Schauder.TaylorWord
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Spatial Taylor coefficients as summed causal shell pairings

The spatial coefficient in Hairer [Hai14, (5.12), (8.20)] is obtained by
spatially differentiating the actual convolution. Spatial derivatives of
the shells have summable L¹ norms. Local compact bounds on the smooth
input suffice; no whole-space Q-distribution hypothesis is used.
-/

public noncomputable section

open MeasureTheory Set
open scoped Convolution Topology

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

private theorem shell_compact (N n : ℕ) : HasCompactSupport (annShellC N n) :=
  hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n

private theorem shell_convolution_hasDerivAt (N n : ℕ) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (i : Fin 3) (x : ParabolicSpace) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∫ w, annShellC N n (x + s • spaceDir i - w) * f w)
      (∫ w, f w * lineIter [spaceDir i] (annShellC N n) (x + t • spaceDir i - w)) t := by
  let v := spaceDir i
  let z := x + t • v
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hcn : ContDiff ℝ 1 (annShellC N n) :=
    (contDiff_annShellC N n).of_le (by simp)
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id t).smul_const v).const_add x
  have hd := ((shell_compact N n).hasFDerivAt_convolution_left L hcn
    (hf.locallyIntegrable (μ := volume)) z).comp_hasDerivAt t hline
  have hDcont : Continuous (fderiv ℝ (annShellC N n)) :=
    hcn.continuous_fderiv one_ne_zero
  have hDint : Integrable (fun w => f w • fderiv ℝ (annShellC N n) (z - w)) :=
    (hf.smul (hDcont.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (((shell_compact N n).fderiv ℝ).comp_homeomorph (Homeomorph.subLeft z)).smul_left
  have hval :
      ((fderiv ℝ (annShellC N n) ⋆[L.precompL ParabolicSpace, volume] f) z) v =
        ∫ w, f w * lineIter [spaceDir i] (annShellC N n) (z - w) := by
    rw [convolution_eq_swap]
    have he : (fun w => L.precompL ParabolicSpace
        (fderiv ℝ (annShellC N n) (z - w)) (f w)) =
        (fun w => f w • fderiv ℝ (annShellC N n) (z - w)) := by
      funext w
      apply ContinuousLinearMap.ext
      intro q
      change _ * f w = f w * _
      exact mul_comm _ _
    rw [he, ContinuousLinearMap.integral_apply hDint]
    simp only [smul_apply, smul_eq_mul, lineIter_cons, lineIter_nil,
      dirDeriv]
    rfl
  have hefun : (fun s : ℝ => (annShellC N n ⋆[L, volume] f) (x + s • v)) =
      (fun s : ℝ => ∫ w, annShellC N n (x + s • v - w) * f w) :=
    funext (fun s => convolution_mul_swap)
  rw [hval] at hd
  simp only [Function.comp_def] at hd
  rw [hefun] at hd
  exact hd

private theorem spatial_shell_integral_abs (N : ℕ) (i : Fin 3) (n : ℕ) :
    (∫ w, |lineIter [spaceDir i] (annShellC N n) w|) =
      (1 / 2 : ℝ) ^ n * ∫ w, |lineIter [spaceDir i] (annKernel0C N) w| := by
  have hh := integral_abs_word_scaledShell (contDiff_annKernel0C N) [i.succ] n
  have hw : indexWeight [i.succ] = 1 := by
    fin_cases i <;> simp [indexWeight_cons, indexWeight_nil, parabolicWeight]
  simp only [List.map_cons, List.map_nil, coordDir_succ, hw, pow_one] at hh
  change (∫ w, |lineIter [spaceDir i] (scaledShell (annKernel0C N) n) w|) = _
  rw [hh]
  have hfactor : (2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ ^ 2) = (1 / 2 : ℝ) ^ n := by
    simp only [one_div, inv_pow]
    field_simp
  calc
    _ = ((2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ ^ 2)) *
        (∫ w, |lineIter [spaceDir i] (annKernel0C N) w|) := by ring
    _ = _ := by rw [hfactor]

private theorem spatial_line_norm (i : Fin 3) (t : ℝ) :
    parabolicNorm (t • spaceDir i) = |t| := by
  simp [parabolicNorm, spaceDir, Pi.single_apply]
  simp only [apply_ite abs, abs_zero]
  simp

private theorem shell_unit_zero (N n : ℕ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : annShellC N n w = 0 :=
  annShellC_eq_zero (lt_of_le_of_lt
    (pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1)) hw)

private theorem derivative_shell_unit_zero (N n : ℕ) (i : Fin 3) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : lineIter [spaceDir i] (annShellC N n) w = 0 :=
  lineIter_eq_zero_of_lt (fun _ hz => shell_unit_zero N n hz) _ hw

private theorem derivative_shell_shift_integrable (N n : ℕ) (i : Fin 3)
    (z : ParabolicSpace) :
    Integrable (fun w => |lineIter [spaceDir i] (annShellC N n) (z - w)|) :=
  ((contDiff_lineIter (contDiff_annShellC N n) _).continuous.comp
    (continuous_const.sub continuous_id)).abs.integrable_of_hasCompactSupport
      (((hasCompactSupport_lineIter (shell_compact N n) _).comp_homeomorph
        (Homeomorph.subLeft z)).abs)

private theorem derivative_shell_pairing_bound (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (i : Fin 3) (x : ParabolicSpace) :
    ∃ B : ℝ, ∀ n : ℕ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      |∫ w, f w * lineIter [spaceDir i] (annShellC N n) (x + t • spaceDir i - w)| ≤
        B * (1 / 2 : ℝ) ^ n := by
  have hcompact : IsCompact {w : ParabolicSpace | parabolicNorm (w - x) ≤ 2} :=
    (Homeomorph.subRight x).isClosedEmbedding.isCompact_preimage
      (isCompact_parabolicNorm_le 2)
  obtain ⟨A, hA⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max A 0 * ∫ w, |lineIter [spaceDir i] (annKernel0C N) w|, ?_⟩
  intro n t ht
  have hφ : Continuous (fun w => lineIter [spaceDir i] (annShellC N n)
      (x + t • spaceDir i - w)) :=
    (contDiff_lineIter (contDiff_annShellC N n) _).continuous.comp
      (continuous_const.sub continuous_id)
  have hφc : HasCompactSupport (fun w => lineIter [spaceDir i] (annShellC N n)
      (x + t • spaceDir i - w)) :=
    (hasCompactSupport_lineIter (shell_compact N n) _).comp_homeomorph
      (Homeomorph.subLeft (x + t • spaceDir i))
  calc
    _ ≤ ∫ w, |f w * lineIter [spaceDir i] (annShellC N n)
        (x + t • spaceDir i - w)| := abs_integral_le_integral_abs
    _ ≤ ∫ w, max A 0 * |lineIter [spaceDir i] (annShellC N n)
        (x + t • spaceDir i - w)| := by
      apply integral_mono (((hf.mul hφ).integrable_of_hasCompactSupport hφc.mul_left).abs)
        ((derivative_shell_shift_integrable N n i _).const_mul _)
      intro w
      change |f w * lineIter [spaceDir i] (annShellC N n)
        (x + t • spaceDir i - w)| ≤ _
      by_cases hw : parabolicNorm (x + t • spaceDir i - w) ≤ 1
      · have hloc : parabolicNorm (w - x) ≤ 2 := by
          have hh := parabolicNorm_add_le (w - (x + t • spaceDir i)) (t • spaceDir i)
          rw [show w - (x + t • spaceDir i) + t • spaceDir i = w - x by abel,
            parabolicNorm_sub_comm w (x + t • spaceDir i), spatial_line_norm] at hh
          have habs : |t| < 1 := abs_lt.2 ht
          linarith
        have hfw : |f w| ≤ max A 0 := by
          have hb : |f w| ≤ A := by simpa only [Real.norm_eq_abs] using hA w hloc
          exact hb.trans (le_max_left _ _)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hfw (abs_nonneg _)
      · simp only [derivative_shell_unit_zero N n i (lt_of_not_ge hw),
          mul_zero, abs_zero, le_refl]
    _ = _ := by
      rw [integral_const_mul, integral_abs_sub_left,
        spatial_shell_integral_abs]
      ring

/-- The spatial derivative shell pairings converge absolutely for locally
continuous input, using only a compact neighbourhood of the base point. -/
theorem summable_hairerSpatialShellPairing (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (i : Fin 3) (x : ParabolicSpace) :
    Summable (fun n : ℕ => ∫ w,
      f w * lineIter [spaceDir i] (annShellC N n) (x - w)) := by
  obtain ⟨B, hB⟩ := derivative_shell_pairing_bound N hf i x
  have hgeom : Summable (fun n : ℕ => B * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left B
  apply hgeom.of_norm_bounded
  intro n
  have hb := hB n 0 (by constructor <;> norm_num)
  simpa only [Real.norm_eq_abs, zero_smul, add_zero] using hb

open scoped ContDiff in
/-- The actual spatial Taylor coefficient is the sum of the spatial
derivative shell pairings [Hai14, (5.12), (8.20)]. -/
theorem hairerSpatialGradient_eq_tsum_shellPairing (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3)
    (x : ParabolicSpace) :
    hairerSpatialGradient N f i x =
      ∑' n : ℕ, ∫ w, f w * lineIter [spaceDir i] (annShellC N n) (x - w) := by
  let F : ℕ → ℝ → ℝ := fun n s =>
    ∫ w, annShellC N n (x + s • spaceDir i - w) * f w
  let F' : ℕ → ℝ → ℝ := fun n s =>
    ∫ w, f w * lineIter [spaceDir i] (annShellC N n) (x + s • spaceDir i - w)
  obtain ⟨B, hB⟩ := derivative_shell_pairing_bound N hf.continuous i x
  have hgeom : Summable (fun n : ℕ => B * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left B
  have he (s : ℝ) (n : ℕ) :
      F n s = ∫ w, annShellC N n w * f (x + s • spaceDir i - w) := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self
        (fun w => annShellC N n w * f (x + s • spaceDir i - w)) volume
        (x + s • spaceDir i))
  have hF0 : Summable (fun n : ℕ => F n 0) := by
    simp_rw [he]
    simp only [zero_smul, add_zero]
    exact (canonicalShell_summable_integral_norm N hf.continuous x).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have hz : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hseries := hasDerivAt_tsum_of_isPreconnected (g := F) (g' := F')
    hgeom isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => shell_convolution_hasDerivAt N n hf.continuous i x s)
    (fun n s hs => by simpa only [Real.norm_eq_abs] using hB n s hs) hz hF0 hz
  have hfun : (fun s : ℝ => ∑' n : ℕ, F n s) =
      fun s => hairerConvolution N f (x + s • spaceDir i) := by
    funext s
    simp_rw [he]
    exact (hairerConvolution_eq_tsum_shellConvolution N hf.continuous _).symm
  rw [hfun] at hseries
  have hline : HasDerivAt (fun s : ℝ => x + s • spaceDir i) (spaceDir i) 0 := by
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (spaceDir i)).const_add x
  have hconv := ((contDiff_hairerConvolution N hf).differentiable (by simp)
    (x + (0 : ℝ) • spaceDir i)).hasFDerivAt.comp_hasDerivAt 0 hline
  simp only [zero_smul, add_zero, Function.comp_def] at hconv
  rw [hairerSpatialGradient_eq_fderiv N hf i x]
  simpa only [F', zero_smul, add_zero, spaceDir] using hconv.unique hseries

end RegularityStructures.Phi43

end
