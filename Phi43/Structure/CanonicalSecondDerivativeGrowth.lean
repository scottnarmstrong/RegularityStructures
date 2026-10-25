/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalConvolutionDerivativeGrowth
public import Phi43.Structure.CanonicalDerivativeGrowthAlgebra
public import Phi43.Structure.CanonicalGammaPrimitiveBounds
public import Phi43.Structure.CanonicalGlobalDerivativeGrowth
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Second derivatives through the causal convolution

The smooth canonical lift needs a whole-space bound for the second ordinary derivative of
`K * (K * zeta)`.  This file derives it from the finite derivative premise on the smooth noise.
It is an analytic helper for the parabolic Taylor remainder, not an additional model-bound
hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology Pointwise

namespace RegularityStructures.Phi43

open RegularityStructures

open scoped ContDiff in
private theorem integrable_hairerKernel_smul_fderiv_at
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : ParabolicSpace) :
    Integrable (fun w => hairerKernel N w • fderiv ℝ f (z - w)) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc := canonicalHairerKernel_hasCompactSupport N
  have hi := canonicalHairerKernel_integrable N
  let S : Set ParabolicSpace := ({z} : Set ParabolicSpace) +
    -tsupport (hairerKernel N)
  have hS : IsCompact S := (isCompact_singleton (x := z)).add hc.isCompact.neg
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hfd.continuousOn
  have hd (w : ParabolicSpace) (hw : hairerKernel N w ≠ 0) :
      ‖fderiv ℝ f (z - w)‖ ≤ max D 0 := by
    apply (hD (z - w) ?_).trans (le_max_left _ _)
    refine Set.mem_add.2 ⟨z, Set.mem_singleton z, -w, ?_, by abel⟩
    simpa only [Set.mem_neg, neg_neg] using
      (subset_tsupport (hairerKernel N) hw :
        w ∈ tsupport (hairerKernel N))
  have hmeas :
      AEStronglyMeasurable
        (fun w => hairerKernel N w • fderiv ℝ f (z - w)) :=
    hi.aestronglyMeasurable.smul
      ((hfd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  refine hi.abs.mul_const (max D 0) |>.mono' hmeas ?_
  filter_upwards [] with w
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hw : hairerKernel N w = 0
  · rw [hw]
    simp only [abs_zero, zero_mul]
    exact le_refl 0
  · exact mul_le_mul_of_nonneg_left (hd w hw) (abs_nonneg _)

open scoped ContDiff in
private theorem hairerConvolution_dirDeriv
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : ParabolicSpace) :
    hairerConvolution N (dirDeriv v f) =
      dirDeriv v (hairerConvolution N f) := by
  funext z
  unfold dirDeriv
  rw [hairerConvolution_eq_convolution, convolution_def,
    fderiv_hairerConvolution N hf z, ContinuousLinearMap.integral_apply]
  · simp only [ContinuousLinearMap.mul_apply']
    rfl
  · exact integrable_hairerKernel_smul_fderiv_at N hf z

open scoped ContDiff in
private theorem contDiff_dirDeriv
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (v : ParabolicSpace) :
    ContDiff ℝ ∞ (dirDeriv v f) := by
  unfold dirDeriv
  simpa [dirDeriv] using
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

open scoped ContDiff in
private theorem dirDeriv_fderiv_bound_of_second
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ℝ) (p : ℕ)
    (hA : ∀ z, ‖fderiv ℝ (fun y => fderiv ℝ f y) z‖ ≤
      A * (1 + parabolicNorm z) ^ p)
    (v : ParabolicSpace) (z : ParabolicSpace) :
    ‖fderiv ℝ (dirDeriv v f) z‖ ≤
      A * (1 + parabolicNorm z) ^ p * ‖v‖ := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by simp) z
  have hconst : DifferentiableAt ℝ (fun _ : ParabolicSpace => v) z :=
    differentiableAt_const v
  have hzero : fderiv ℝ (fun _ : ParabolicSpace => v) z = 0 := by
    simp
  have he := fderiv_clm_apply hfd hconst
  rw [show dirDeriv v f = fun y => fderiv ℝ f y v by rfl,
    he, hzero]
  simp only [ContinuousLinearMap.comp_zero, zero_add]
  calc
    ‖(fderiv ℝ (fun y => fderiv ℝ f y) z).flip v‖ ≤
        ‖fderiv ℝ (fun y => fderiv ℝ f y) z‖ * ‖v‖ := by
          apply ContinuousLinearMap.opNorm_le_bound
          · positivity
          intro w
          rw [ContinuousLinearMap.flip_apply]
          calc
            ‖(fderiv ℝ (fun y => fderiv ℝ f y) z) w v‖ ≤
                ‖(fderiv ℝ (fun y => fderiv ℝ f y) z) w‖ * ‖v‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ (‖fderiv ℝ (fun y => fderiv ℝ f y) z‖ * ‖w‖) * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            _ = ‖fderiv ℝ (fun y => fderiv ℝ f y) z‖ * ‖v‖ * ‖w‖ := by ring
    _ ≤ (A * (1 + parabolicNorm z) ^ p) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hA z) (norm_nonneg _)

open scoped ContDiff in
private theorem polyBounded_second_convolution
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (p : ℕ) (hC : 0 ≤ C)
    (hdir : ∀ v z, ‖fderiv ℝ (dirDeriv v f) z‖ ≤
      C * (1 + parabolicNorm z) ^ p * ‖v‖) :
    PolyBounded (fun z => ‖iteratedFDeriv ℝ 2 (hairerConvolution N f) z‖) := by
  let F := hairerConvolution N f
  have hF : ContDiff ℝ ∞ F := contDiff_hairerConvolution N hf
  let L : ℝ := ∫ w, |hairerKernel N w|
  have hL : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hbase (z : ParabolicSpace) :
      0 ≤ L * C * 2 ^ p * (1 + parabolicNorm z) ^ p := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hL hC) (by positivity))
      (pow_nonneg (by linarith [parabolicNorm_nonneg z]) p)
  have hfirst (v z : ParabolicSpace) :
      ‖fderiv ℝ (dirDeriv v F) z‖ ≤
        L * C * 2 ^ p * (1 + parabolicNorm z) ^ p * ‖v‖ := by
    rw [← hairerConvolution_dirDeriv N hf v]
    have hdir' : ∀ w, ‖fderiv ℝ (dirDeriv v f) w‖ ≤
        (C * ‖v‖) * (1 + parabolicNorm w) ^ p := by
      intro w
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdir v w
    have hh := norm_fderiv_hairerConvolution_le N (contDiff_dirDeriv hf v)
      (C * ‖v‖) p hdir' z
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using hh
  have hA (z : ParabolicSpace) :
      ‖fderiv ℝ (fun y => fderiv ℝ F y) z‖ ≤
        L * C * 2 ^ p * (1 + parabolicNorm z) ^ p := by
    apply ContinuousLinearMap.opNorm_le_bound
    · exact hbase z
    intro w
    apply ContinuousLinearMap.opNorm_le_bound
    · exact mul_nonneg (hbase z) (norm_nonneg _)
    intro v
    have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
      (hF.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by simp) z
    have hconst : DifferentiableAt ℝ (fun _ : ParabolicSpace => v) z :=
      differentiableAt_const v
    have hzero : fderiv ℝ (fun _ : ParabolicSpace => v) z = 0 := by
      simp
    have he := fderiv_clm_apply hfd hconst
    have hflip :
        ‖(fderiv ℝ (fun y => fderiv ℝ F y) z).flip v‖ ≤
          L * C * 2 ^ p * (1 + parabolicNorm z) ^ p * ‖v‖ := by
      have heq : fderiv ℝ (dirDeriv v F) z =
          (fderiv ℝ (fun y => fderiv ℝ F y) z).flip v := by
        rw [show dirDeriv v F = fun y => fderiv ℝ F y v by rfl,
          he, hzero]
        simp only [ContinuousLinearMap.comp_zero, zero_add]
      calc
        ‖(fderiv ℝ (fun y => fderiv ℝ F y) z).flip v‖ =
            ‖fderiv ℝ (dirDeriv v F) z‖ := congrArg norm heq.symm
        _ ≤ _ := hfirst v z
    calc
      ‖(fderiv ℝ (fun y => fderiv ℝ F y) z) w v‖ ≤
          ‖(fderiv ℝ (fun y => fderiv ℝ F y) z).flip v‖ * ‖w‖ :=
        by
          change ‖((fderiv ℝ (fun y => fderiv ℝ F y) z).flip v) w‖ ≤ _
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * C * 2 ^ p * (1 + parabolicNorm z) ^ p * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hflip (norm_nonneg _)
      _ ≤ (L * C * 2 ^ p * (1 + parabolicNorm z) ^ p) * ‖w‖ * ‖v‖ := by
        ring_nf
        exact le_rfl
  refine ⟨(hF.continuous_iteratedFDeriv (m := 2) (by simp)).norm.measurable,
    L * C * 2 ^ p, p, ?_⟩
  intro z
  have hz := hA z
  change ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ _ at hz
  have hnorm : ‖iteratedFDeriv ℝ 2 F z‖ =
      ‖fderiv ℝ (fderiv ℝ F) z‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [← hnorm] at hz
  simpa only [F, abs_of_nonneg (norm_nonneg _)] using hz

open scoped ContDiff in
private theorem canonicalNoise_dirDeriv_fderiv_bound
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (v z : ParabolicSpace) :
    ‖fderiv ℝ (dirDeriv v noise.zeta) z‖ ≤
      C * (1 + parabolicNorm z) ^ p * ‖v‖ := by
  have hf := noise.smooth
  have hfd : DifferentiableAt ℝ (fderiv ℝ noise.zeta) z :=
    (hf.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by simp) z
  have hconst : DifferentiableAt ℝ (fun _ : ParabolicSpace => v) z :=
    differentiableAt_const v
  have hzero : fderiv ℝ (fun _ : ParabolicSpace => v) z = 0 := by
    simp
  have he := fderiv_clm_apply hfd hconst
  rw [show dirDeriv v noise.zeta = fun y => fderiv ℝ noise.zeta y v by rfl,
    he, hzero]
  simp only [ContinuousLinearMap.comp_zero, zero_add]
  calc
    ‖(fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z).flip v‖ ≤
        ‖fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z‖ * ‖v‖ := by
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      intro w
      calc
        ‖(fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z) w v‖ ≤
            ‖(fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z) w‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z‖ * ‖w‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = ‖fderiv ℝ (fun y => fderiv ℝ noise.zeta y) z‖ * ‖v‖ * ‖w‖ := by
          ring
    _ = ‖iteratedFDeriv ℝ 2 noise.zeta z‖ * ‖v‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    _ ≤ (C * (1 + parabolicNorm z) ^ p) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hg 2 (by omega) z) (norm_nonneg _)

private theorem parabolicNorm_smul_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : ParabolicSpace) :
    parabolicNorm (t • v) ≤ parabolicNorm v := by
  unfold parabolicNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply,
    abs_mul, abs_of_nonneg ht0, Real.sqrt_mul (by positivity)]
  have hts : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).2 ht1
  have hsum : (∑ i : Fin 3, t * |v.2 i|) ≤ ∑ i : Fin 3, |v.2 i| := by
    simpa only [mul_comm] using
      (Finset.sum_le_sum fun i _ =>
        mul_le_of_le_one_right (abs_nonneg (v.2 i)) ht1)
  have hs : Real.sqrt t * Real.sqrt |v.1| ≤ Real.sqrt |v.1| :=
    by simpa only [mul_comm] using
      (mul_le_of_le_one_right (Real.sqrt_nonneg |v.1|) hts)
  exact add_le_add hs hsum

open scoped ContDiff in
private theorem canonicalParabolicTaylor_remainder
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ℝ) (p : ℕ) (hA : 0 ≤ A)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤
      A * (1 + parabolicNorm z) ^ p)
    (x y : ParabolicSpace) (hxy : parabolicNorm (y - x) ≤ 1) :
    |f y - f x - fderiv ℝ f x (y - x)| ≤
      A * 2 ^ p * (1 + parabolicNorm x) ^ p *
        parabolicNorm (y - x) ^ 2 := by
  have hpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      parabolicNorm (x + t • (y - x)) ≤ parabolicNorm x + 1 := by
    calc
      parabolicNorm (x + t • (y - x)) ≤
          parabolicNorm x + parabolicNorm (t • (y - x)) :=
        parabolicNorm_add_le _ _
      _ ≤ parabolicNorm x + 1 := by
        linarith [parabolicNorm_smul_unit ht.1 ht.2 (y - x), hxy]
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ 2 f (x + t • (y - x))‖ ≤
        A * 2 ^ p * (1 + parabolicNorm x) ^ p := by
    have harg : 1 + parabolicNorm (x + t • (y - x)) ≤
        2 * (1 + parabolicNorm x) := by
      have hx := parabolicNorm_nonneg x
      linarith [hpath t ht]
    have hp := pow_le_pow_left₀
      (by linarith [parabolicNorm_nonneg (x + t • (y - x))]) harg p
    calc
      _ ≤ A * (1 + parabolicNorm (x + t • (y - x))) ^ p := h2 _
      _ ≤ A * (2 * (1 + parabolicNorm x)) ^ p :=
        mul_le_mul_of_nonneg_left hp hA
      _ = A * 2 ^ p * (1 + parabolicNorm x) ^ p := by rw [mul_pow]; ring
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := x) (y := y - x) (n := 1)
      (fun t ht => (hf.contDiffAt (x := x + t • (y - x))).of_le (by simp))
  have hxy' : y = x + (y - x) := by abel
  rw [← hxy'] at htaylor
  norm_num [Finset.sum_range_succ, Nat.factorial] at htaylor
  have hlin : (fderiv ℝ f x) y - (fderiv ℝ f x) x =
      (fderiv ℝ f x) (y - x) := by rw [map_sub]
  rw [hlin] at htaylor
  have hrem : f y - f x - fderiv ℝ f x (y - x) =
      ∫ t in (0 : ℝ)..1,
        (1 - t) * iteratedFDeriv ℝ 2 f (x + t • (y - x))
          (fun _ => y - x) := by
    linarith [htaylor]
  rw [hrem]
  have hi : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(1 - t) * iteratedFDeriv ℝ 2 f (x + t • (y - x))
        (fun _ => y - x)| ≤
        A * 2 ^ p * (1 + parabolicNorm x) ^ p *
          parabolicNorm (y - x) ^ 2 := by
    intro t ht
    have hcoef : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have htime : |(y - x).1| ≤ 1 := by
      have hs : Real.sqrt |(y - x).1| ≤ parabolicNorm (y - x) := by
        unfold parabolicNorm
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hsq := Real.sq_sqrt (abs_nonneg (y - x).1)
      have hsn := Real.sqrt_nonneg |(y - x).1|
      nlinarith
    have hvec : ‖y - x‖ ≤ parabolicNorm (y - x) :=
      RegularityStructures.norm_le_parabolicNorm htime
    have hline := (iteratedFDeriv ℝ 2 f
      (x + t • (y - x))).le_opNorm (fun _ : Fin 2 => y - x)
    have hvec2 : ‖y - x‖ ^ 2 ≤ parabolicNorm (y - x) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hvec 2
    calc
      _ ≤ |1 - t| * ‖iteratedFDeriv ℝ 2 f (x + t • (y - x))‖ *
          ‖y - x‖ ^ 2 := by
        have hline' := mul_le_mul_of_nonneg_left hline (norm_nonneg (1 - t))
        calc
          _ ≤ (1 - t) * (‖iteratedFDeriv ℝ 2 f
              (x + t • (y - x))‖ * (‖y - x‖ * ‖y - x‖)) := by
            simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef,
              Fin.prod_univ_two] using hline'
          _ = _ := by
            rw [pow_two]
            rw [abs_of_nonneg hcoef]
            ring
      _ ≤ A * 2 ^ p * (1 + parabolicNorm x) ^ p *
          parabolicNorm (y - x) ^ 2 := by
        have hcoef' : 1 - t ≤ 1 := by linarith [ht.1]
        have hcoef'' : |1 - t| ≤ 1 := by
          simpa only [abs_of_nonneg hcoef] using hcoef'
        have hbound' := hbound t ht
        have hnorm0 : 0 ≤ ‖iteratedFDeriv ℝ 2 f
            (x + t • (y - x))‖ := norm_nonneg _
        have hv0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
        calc
          _ ≤ |1 - t| * ‖iteratedFDeriv ℝ 2 f
              (x + t • (y - x))‖ * parabolicNorm (y - x) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hvec2
              (mul_nonneg (abs_nonneg _) hnorm0)
          _ ≤ ‖iteratedFDeriv ℝ 2 f (x + t • (y - x))‖ *
              parabolicNorm (y - x) ^ 2 := by
            calc
              _ = (‖iteratedFDeriv ℝ 2 f
                  (x + t • (y - x))‖ * |1 - t|) *
                  parabolicNorm (y - x) ^ 2 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_of_le_one_right hnorm0 hcoef'') (pow_nonneg hv0 2)
          _ ≤ (A * 2 ^ p * (1 + parabolicNorm x) ^ p) *
              parabolicNorm (y - x) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hbound'
              (pow_nonneg hv0 2)
          _ = _ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t => (1 - t) * iteratedFDeriv ℝ 2 f
      (x + t • (y - x)) (fun _ => y - x))
    (C := A * 2 ^ p * (1 + parabolicNorm x) ^ p *
      parabolicNorm (y - x) ^ 2)
    (fun t ht => by
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht'
      simpa only [Real.norm_eq_abs] using hi t ht')
  have hC : 0 ≤ A * 2 ^ p * (1 + parabolicNorm x) ^ p *
      parabolicNorm (y - x) ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (by positivity))
        (pow_nonneg (by linarith [parabolicNorm_nonneg x]) p))
      (pow_nonneg (parabolicNorm_nonneg _) 2)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC, sub_zero, abs_one, mul_one] using hint

/-! The source-only weighted estimate for the constant `I(Ψ)` character. -/
open scoped ContDiff in
theorem canonicalGamma_cPsi_growth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ p : ℕ, ∀ x y,
      parabolicNorm (y - x) ≤ 1 →
        |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsi| ≤
          B * (1 + parabolicNorm x)^p *
            parabolicNorm (y - x)^homogeneity κ .iPsi := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hC : 0 ≤ C := by
    have h0 := hg 0 (by omega) (0 : ParabolicSpace)
    simpa only [norm_iteratedFDeriv_zero, parabolicNorm_zero, add_zero,
      one_pow, mul_one] using
      (norm_nonneg (iteratedFDeriv ℝ 0 noise.zeta 0)).trans h0
  have hpsi : ContDiff ℝ ∞ D.globalPsi := by
    simpa [D, CanonicalData.globalPiBasis] using
      (canonicalGlobalPiBasis_smooth N (κ := κ) noise .psi)
  have hnoiseDir (v z : ParabolicSpace) :
      ‖fderiv ℝ (dirDeriv v noise.zeta) z‖ ≤
        C * (1 + parabolicNorm z) ^ q * ‖v‖ :=
    canonicalNoise_dirDeriv_fderiv_bound noise C q hg v z
  have hpsi2 : PolyBounded (fun z =>
      ‖iteratedFDeriv ℝ 2 D.globalPsi z‖) := by
    change PolyBounded (fun z =>
      ‖iteratedFDeriv ℝ 2 (hairerConvolution N noise.zeta) z‖)
    exact polyBounded_second_convolution N noise.smooth C q hC hnoiseDir
  obtain ⟨_, A₂, p₂, hA₂⟩ := hpsi2
  have hA₂0 : 0 ≤ A₂ := by
    have h0 := hA₂ (0 : ParabolicSpace)
    have h0' : ‖iteratedFDeriv ℝ 2 D.globalPsi 0‖ ≤ A₂ := by
      simpa only [parabolicNorm_zero, add_zero, one_pow, mul_one,
        abs_of_nonneg (norm_nonneg _)] using h0
    exact (norm_nonneg _).trans h0'
  have hpsi2' (z : ParabolicSpace) :
      ‖fderiv ℝ (fun y => fderiv ℝ D.globalPsi y) z‖ ≤
        A₂ * (1 + parabolicNorm z) ^ p₂ := by
    have heq : ‖iteratedFDeriv ℝ 2 D.globalPsi z‖ =
        ‖fderiv ℝ (fderiv ℝ D.globalPsi) z‖ := by
      have hnorm : ‖iteratedFDeriv ℝ 2 D.globalPsi z‖ =
          ‖fderiv ℝ (fderiv ℝ D.globalPsi) z‖ := by
        rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      exact hnorm
    rw [show (fun y => fderiv ℝ D.globalPsi y) = fderiv ℝ D.globalPsi by rfl]
    rw [← heq]
    simpa only [abs_of_nonneg (norm_nonneg _)] using hA₂ z
  have hglobalDir (v z : ParabolicSpace) :
      ‖fderiv ℝ (dirDeriv v D.globalPsi) z‖ ≤
        A₂ * (1 + parabolicNorm z) ^ p₂ * ‖v‖ :=
    dirDeriv_fderiv_bound_of_second hpsi A₂ p₂ hpsi2' v z
  have hiPsi2 : PolyBounded (fun z =>
      ‖iteratedFDeriv ℝ 2 D.globalIPsi z‖) := by
    change PolyBounded (fun z =>
      ‖iteratedFDeriv ℝ 2 (hairerConvolution N D.globalPsi) z‖)
    exact polyBounded_second_convolution N hpsi A₂ p₂ hA₂0 hglobalDir
  obtain ⟨_, A₃, p₃, hA₃⟩ := hiPsi2
  have hA₃0 : 0 ≤ A₃ := by
    have h0 := hA₃ (0 : ParabolicSpace)
    have h0' : ‖iteratedFDeriv ℝ 2 D.globalIPsi 0‖ ≤ A₃ := by
      simpa only [parabolicNorm_zero, add_zero, one_pow, mul_one,
        abs_of_nonneg (norm_nonneg _)] using h0
    exact (norm_nonneg _).trans h0'
  obtain ⟨_, A₁, p₁, hA₁⟩ :=
    canonicalGlobalPiBasis_derivative_growth N κ noise C q hg .iPsi
  have hA₁0 : 0 ≤ A₁ := by
    have h0 := hA₁ (0 : ParabolicSpace)
    have h0' : ‖fderiv ℝ D.globalIPsi 0‖ ≤ A₁ := by
      simpa only [D, CanonicalData.globalPiBasis, parabolicNorm_zero,
        add_zero, one_pow, mul_one, abs_of_nonneg (norm_nonneg _)] using h0
    exact (norm_nonneg _).trans h0'
  let p := p₁ + p₃
  let B := A₃ * 2 ^ p₃ + A₁
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB0, p, ?_⟩
  intro x y hxy
  have h2 (z : ParabolicSpace) :
      ‖iteratedFDeriv ℝ 2 D.globalIPsi z‖ ≤
        A₃ * (1 + parabolicNorm z) ^ p₃ := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using hA₃ z
  have hrem := canonicalParabolicTaylor_remainder
    (f := D.globalIPsi) (by simpa [D, CanonicalData.globalPiBasis] using
      canonicalGlobalPiBasis_smooth N (κ := κ) noise .iPsi)
    A₃ p₃ hA₃0 h2 x y hxy
  have hfirst (z : ParabolicSpace) :
      ‖fderiv ℝ D.globalIPsi z‖ ≤ A₁ * (1 + parabolicNorm z) ^ p₁ := by
    simpa only [D, CanonicalData.globalPiBasis,
      abs_of_nonneg (norm_nonneg _)] using hA₁ z
  have htime : |(y - x).1| ≤ parabolicNorm (y - x) ^ 2 := by
    have hs : Real.sqrt |(y - x).1| ≤ parabolicNorm (y - x) := by
      unfold parabolicNorm
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hsq := Real.sq_sqrt (abs_nonneg (y - x).1)
    have hsn := Real.sqrt_nonneg |(y - x).1|
    nlinarith
  have hspvec : ((0 : ℝ), (y - x).2) =
      ∑ i : Fin 3, (y - x).2 i • (0, Pi.single i 1) := by
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp
    · funext j
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd,
        Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b hb hbj
        rw [Pi.single_eq_of_ne hbj.symm]
        simp
      · simp
  have hsp : fderiv ℝ D.globalIPsi x ((0 : ℝ), (y - x).2) =
      ∑ i : Fin 3, fderiv ℝ D.globalIPsi x (0, Pi.single i 1) *
        (y - x).2 i := by
    rw [hspvec, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have htimeNorm : ‖((y - x).1, (0 : Fin 3 → ℝ))‖ = |(y - x).1| := by
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hgrad (i : Fin 3) : hairerSpatialGradient N D.globalPsi i =
      fun z => fderiv ℝ D.globalIPsi z (0, Pi.single i 1) := by
    funext z
    rw [hairerSpatialGradient_eq_fderiv N hpsi i]
    rfl
  have hdecomp :
      D.globalIPsi y - D.globalIPsi x -
          ∑ i : Fin 3, fderiv ℝ D.globalIPsi x (0, Pi.single i 1) *
            (parabolicCoords y i.succ - parabolicCoords x i.succ) =
        (D.globalIPsi y - D.globalIPsi x -
            fderiv ℝ D.globalIPsi x (y - x)) +
          fderiv ℝ D.globalIPsi x ((y - x).1, (0 : Fin 3 → ℝ)) := by
    have hcoord (i : Fin 3) :
        parabolicCoords y i.succ - parabolicCoords x i.succ =
          (y - x).2 i := by
      fin_cases i <;> simp [parabolicCoords]
    simp_rw [hcoord]
    rw [← hsp]
    have hv : y - x = ((y - x).1, (0 : Fin 3 → ℝ)) +
        ((0 : ℝ), (y - x).2) := by
      apply Prod.ext
      · simp
      · funext i
        simp
    rw [hv]
    rw [map_add]
    simp only [Prod.fst_add, Prod.snd_add, zero_add, add_zero]
    ring
  rw [canonicalGamma_cPsi_eq_iPsi]
  change |D.canonicalPi x (basis .iPsi) y| ≤ _
  rw [CanonicalData.canonicalPi_basis]
  have hi0 : 0 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    have hk : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith
  have hi1 : 1 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    have hk : κ.1 < 1 / 16 := by
      simpa [kappa₀] using kappa_lt_kappa₀ κ
    linarith
  change |hairerConvolution N D.localPsi y -
      ((if 0 < homogeneity κ .iPsi then hairerConvolution N D.localPsi x else 0) +
        (if 1 < homogeneity κ .iPsi then ∑ i : Fin 3,
          hairerSpatialGradient N D.localPsi i x *
            (parabolicCoords y i.succ - parabolicCoords x i.succ) else 0))| ≤ _
  simp only [hi0, hi1, ite_true]
  rw [CanonicalData.localPsi_eq_globalPsi]
  change |D.globalIPsi y - (D.globalIPsi x + ∑ i : Fin 3,
    hairerSpatialGradient N D.globalPsi i x *
      (parabolicCoords y i.succ - parabolicCoords x i.succ))| ≤ _
  simp_rw [hgrad]
  rw [show D.globalIPsi y - (D.globalIPsi x + ∑ i : Fin 3,
      (fderiv ℝ D.globalIPsi x) (0, Pi.single i 1) *
        (parabolicCoords y i.succ - parabolicCoords x i.succ)) =
      D.globalIPsi y - D.globalIPsi x - ∑ i : Fin 3,
        (fderiv ℝ D.globalIPsi x) (0, Pi.single i 1) *
          (parabolicCoords y i.succ - parabolicCoords x i.succ) by ring]
  rw [hdecomp]
  calc
    _ ≤ |D.globalIPsi y - D.globalIPsi x -
          fderiv ℝ D.globalIPsi x (y - x)| +
        |fderiv ℝ D.globalIPsi x ((y - x).1, (0 : Fin 3 → ℝ))| :=
      abs_add_le _ _
    _ ≤ A₃ * 2 ^ p₃ * (1 + parabolicNorm x) ^ p₃ *
          parabolicNorm (y - x) ^ 2 +
        A₁ * (1 + parabolicNorm x) ^ p₁ *
          |(y - x).1| := by
      refine add_le_add hrem ?_
      calc
        |fderiv ℝ D.globalIPsi x ((y - x).1, (0 : Fin 3 → ℝ))| ≤
            ‖fderiv ℝ D.globalIPsi x‖ *
              ‖((y - x).1, (0 : Fin 3 → ℝ))‖ :=
          by
            simpa only [Real.norm_eq_abs] using
              (ContinuousLinearMap.le_opNorm (fderiv ℝ D.globalIPsi x)
                ((y - x).1, (0 : Fin 3 → ℝ)))
        _ = ‖fderiv ℝ D.globalIPsi x‖ * |(y - x).1| := by rw [htimeNorm]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hfirst x) (abs_nonneg _)
    _ ≤ B * (1 + parabolicNorm x) ^ p *
          parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
      have hu : 1 ≤ 1 + parabolicNorm x := by linarith [parabolicNorm_nonneg x]
      have hp₁ := pow_le_pow_right₀ hu (Nat.le_add_right p₁ p₃)
      have hp₃ := pow_le_pow_right₀ hu (Nat.le_add_left p₃ p₁)
      have hd0 := parabolicNorm_nonneg (y - x)
      have hd2 : parabolicNorm (y - x) ^ 2 ≤
          parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
        have hα0 : 0 ≤ homogeneity κ .iPsi := by
          simp only [homogeneity]
          have hk : κ.1 < 1 / 16 := by
            simpa [kappa₀] using kappa_lt_kappa₀ κ
          linarith
        have hα2 : homogeneity κ .iPsi ≤ 2 := by
          simp only [homogeneity]
          linarith [kappa_pos κ]
        have hpow := Real.rpow_le_rpow_of_exponent_ge'
          (x := parabolicNorm (y - x)) (y := (2 : ℝ))
          (z := homogeneity κ .iPsi) hd0 hxy hα0 hα2
        rw [← Real.rpow_natCast]
        exact hpow
      have hdt : |(y - x).1| ≤ parabolicNorm (y - x) ^ 2 := htime
      calc
        _ ≤ A₃ * 2 ^ p₃ * (1 + parabolicNorm x) ^ p₃ *
              parabolicNorm (y - x) ^ 2 +
            A₁ * (1 + parabolicNorm x) ^ p₁ *
              parabolicNorm (y - x) ^ 2 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hdt
            (by positivity)) _
        _ ≤ A₃ * 2 ^ p₃ * (1 + parabolicNorm x) ^ p *
              parabolicNorm (y - x) ^ 2 +
            A₁ * (1 + parabolicNorm x) ^ p *
              parabolicNorm (y - x) ^ 2 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp₃
                (mul_nonneg hA₃0 (by positivity)))
              (pow_nonneg (parabolicNorm_nonneg _) 2)
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp₁ hA₁0)
              (pow_nonneg (parabolicNorm_nonneg _) 2)
        _ = B * (1 + parabolicNorm x) ^ p *
              parabolicNorm (y - x) ^ 2 := by
          dsimp [B, p]
          ring
        _ ≤ B * (1 + parabolicNorm x) ^ p *
              parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
          exact mul_le_mul_of_nonneg_left hd2 (by positivity)

end RegularityStructures.Phi43

end
