/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Elementary product-measure estimates

The square-of-the-mean estimate below is the Cauchy--Schwarz step used in variance tensorisation. It
is proved here explicitly so that later Gaussian product arguments do not hide Jensen's inequality
in a target predicate. The finite-product argument is the one used for the standard Gaussian measure
in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

theorem integral_sq_le_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have hga : MemLp (fun x => |g x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hg.abs using 1
    · funext x
      rfl
    · norm_num
  have hconst : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    exact memLp_const (p := ENNReal.ofReal (2 : ℝ)) 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (ae_of_all _ fun x => abs_nonneg (g x))
    (ae_of_all _ fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hga hconst
  have h' :
      |∫ x, g x ∂μ| ≤
        (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    calc
      |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |g x| * (1 : ℝ) ∂μ := by
        congr 1
        funext x
        ring
      _ ≤ (∫ x, |g x| ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := h
      _ = (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [integral_const]
        simp only [MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one,
          one_smul, one_rpow]
        have hint : (∫ x, |g x| ^ 2 ∂μ) = ∫ x, (g x) ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact sq_abs (g x)
        calc
          _ = (∫ x, |g x| ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by simp
          _ = (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := congrArg
            (fun t : ℝ => t ^ (1 / 2 : ℝ)) hint
  have hnonneg : 0 ≤ ∫ x, (g x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (g x))
  have hsquare : |∫ x, g x ∂μ| ^ 2 ≤
      ((∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h'
  rw [sq_abs] at hsquare
  simpa only [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg] using hsquare

theorem variance_prod_le_sum_slice_variances
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (hmean_fst : MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ)
    (hmean_snd : MemLp (fun y => ∫ x, f (x, y) ∂μ) 2 ν)
    (hfx : ∀ x, MemLp (fun y => f (x, y)) 2 ν)
    (hfy : ∀ y, MemLp (fun x => f (x, y)) 2 μ) :
    Var[f; μ.prod ν] ≤
      (∫ x, Var[fun y => f (x, y); ν] ∂μ) +
        ∫ y, Var[fun x => f (x, y); μ] ∂ν := by
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂ν
  let k : β → ℝ := fun y => ∫ x, f (x, y) ∂μ
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hf2 : Integrable (fun z => f z ^ 2) (μ.prod ν) := hf.integrable_sq
  have hg : Integrable g μ := by
    simpa [g] using hfi.integral_prod_left
  have hk : Integrable k ν := by
    simpa [k] using hfi.integral_prod_right
  have hg2_bound : Integrable
      (fun x => ∫ y, f (x, y) ^ 2 ∂ν) μ := by
    simpa using hf2.integral_prod_left
  have hk2_bound : Integrable
      (fun y => ∫ x, f (x, y) ^ 2 ∂μ) ν := by
    simpa using hf2.integral_prod_right
  have hg2 : Integrable (fun x => g x ^ 2) μ := by
    refine hg2_bound.mono' (hg.aestronglyMeasurable.pow 2) ?_
    filter_upwards [] with x
    have hx : 0 ≤ g x ^ 2 := sq_nonneg _
    simpa [g, Real.norm_eq_abs, abs_of_nonneg hx] using
      (integral_sq_le_integral_sq (hfx x))
  have hk2 : Integrable (fun y => k y ^ 2) ν := by
    refine hk2_bound.mono' (hk.aestronglyMeasurable.pow 2) ?_
    filter_upwards [] with y
    have hy : 0 ≤ k y ^ 2 := sq_nonneg _
    simpa [k, Real.norm_eq_abs, abs_of_nonneg hy] using
      (integral_sq_le_integral_sq (hfy y))
  have hfg : MemLp (fun z => f z - k z.2) 2 (μ.prod ν) :=
    hf.sub (hmean_snd.comp_snd μ)
  have hfk : Integrable (fun z => (f z - k z.2) ^ 2) (μ.prod ν) :=
    hfg.integrable_sq
  have hfg_prod : Integrable
      (fun x => ∫ y, (f (x, y) - k y) ^ 2 ∂ν) μ := by
    simpa using hfk.integral_prod_left
  have hmean : ∫ z, f z ∂(μ.prod ν) = ∫ x, g x ∂μ := by
    simpa [g] using (integral_prod _ hfi)
  have hmean' : ∫ z, f z ∂(μ.prod ν) = ∫ y, k y ∂ν := by
    simpa [k] using (integral_prod_symm _ hfi)
  have hcenter : ∀ x,
      (g x - ∫ z, f z ∂(μ.prod ν)) ^ 2 ≤
        ∫ y, (f (x, y) - k y) ^ 2 ∂ν := by
    intro x
    have hslice : MemLp (fun y => f (x, y) - k y) 2 ν :=
      (hfx x).sub hmean_snd
    have hj := integral_sq_le_integral_sq hslice
    have hsub : ∫ y, (f (x, y) - k y) ∂ν =
        g x - ∫ y, k y ∂ν := by
      rw [integral_sub ((hfx x).integrable (by norm_num))
        (hmean_snd.integrable (by norm_num))]
    calc
      (g x - ∫ z, f z ∂(μ.prod ν)) ^ 2 =
          (∫ y, (f (x, y) - k y) ∂ν) ^ 2 := by rw [hmean', ← hsub]
      _ ≤ _ := hj
  have hcenter_int :
      ∫ x, (g x - ∫ z, f z ∂(μ.prod ν)) ^ 2 ∂μ ≤
        ∫ x, ∫ y, (f (x, y) - k y) ^ 2 ∂ν ∂μ := by
    have hleft : Integrable (fun x =>
        (g x - ∫ z, f z ∂(μ.prod ν)) ^ 2) μ := by
      simpa [g] using
        (hmean_fst.sub (memLp_const (∫ z, f z ∂(μ.prod ν)))).integrable_sq
    exact integral_mono hleft hfg_prod (fun x => hcenter x)
  have hvar_g_int : Var[g; μ] =
      ∫ x, (g x - ∫ x, g x ∂μ) ^ 2 ∂μ :=
    variance_eq_integral hmean_fst.aemeasurable
  have hcenter_rhs :
      ∫ x, ∫ y, (f (x, y) - k y) ^ 2 ∂ν ∂μ =
        (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ y, k y ^ 2 ∂ν := by
    have hcross : Integrable (fun z => f z * k z.2) (μ.prod ν) :=
      memLp_one_iff_integrable.1 (hf.mul (hmean_snd.comp_snd μ))
    have hcross_integral :
        ∫ z, f z * k z.2 ∂(μ.prod ν) = ∫ y, k y ^ 2 ∂ν := by
      rw [integral_prod_symm _ hcross]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const]
      simp [k]
      ring
    calc
      _ = ∫ z, (f z - k z.2) ^ 2 ∂(μ.prod ν) :=
        (integral_prod _ hfk).symm
      _ = ∫ z, f z ^ 2 - 2 * (f z * k z.2) + k z.2 ^ 2 ∂(μ.prod ν) := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = (∫ z, f z ^ 2 ∂(μ.prod ν)) -
          2 * (∫ z, f z * k z.2 ∂(μ.prod ν)) +
          ∫ z, k z.2 ^ 2 ∂(μ.prod ν) := by
        have hadd := integral_add (hf2.sub (hcross.const_mul 2)) (hk2.comp_snd μ)
        have hsub := integral_sub hf2 (hcross.const_mul 2)
        calc
          _ = (∫ z, f z ^ 2 - 2 * (f z * k z.2) ∂(μ.prod ν)) +
              ∫ z, k z.2 ^ 2 ∂(μ.prod ν) := by
            simpa [Pi.add_apply] using hadd
          _ = _ := by
            rw [hsub, integral_const_mul]
      _ = (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ y, k y ^ 2 ∂ν := by
        have hks : ∫ z, k z.2 ^ 2 ∂(μ.prod ν) = ∫ y, k y ^ 2 ∂ν := by
          simpa using integral_fun_snd (μ := μ) (ν := ν) (fun y => k y ^ 2)
        rw [hcross_integral, hks]
        ring
  have hcenter_bound : Var[g; μ] ≤
      (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ y, k y ^ 2 ∂ν := by
    rw [hvar_g_int, ← hmean]
    rw [← hcenter_rhs]
    exact hcenter_int
  have hvariance_bound :
      (∫ x, g x ^ 2 ∂μ) - (∫ z, f z ∂(μ.prod ν)) ^ 2 ≤
        (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ y, k y ^ 2 ∂ν := by
    have hvg : Var[g; μ] =
        (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 := by
      simpa [g] using (variance_eq_sub hmean_fst)
    calc
      _ = Var[g; μ] := by rw [hvg, hmean]
      _ ≤ _ := hcenter_bound
  have hvar_f : Var[f; μ.prod ν] =
      (∫ z, f z ^ 2 ∂(μ.prod ν)) - (∫ z, f z ∂(μ.prod ν)) ^ 2 :=
    variance_eq_sub hf
  have hvar_x :
      (∫ x, Var[fun y => f (x, y); ν] ∂μ) =
        (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ x, g x ^ 2 ∂μ := by
    have heq : (fun x => Var[fun y => f (x, y); ν]) =
        (fun x => (∫ y, f (x, y) ^ 2 ∂ν) - g x ^ 2) := by
      funext x
      simpa [g] using (variance_eq_sub (hfx x))
    rw [heq, integral_sub]
    · rw [integral_prod _ hf2]
    · exact hg2_bound
    · exact hg2
  have hvar_y :
      (∫ y, Var[fun x => f (x, y); μ] ∂ν) =
        (∫ z, f z ^ 2 ∂(μ.prod ν)) - ∫ y, k y ^ 2 ∂ν := by
    have heq : (fun y => Var[fun x => f (x, y); μ]) =
        (fun y => (∫ x, f (x, y) ^ 2 ∂μ) - k y ^ 2) := by
      funext y
      simpa [k] using (variance_eq_sub (hfy y))
    rw [heq, integral_sub]
    · rw [integral_prod_symm _ hf2]
    · exact hk2_bound
    · exact hk2
  rw [hvar_f, hvar_x, hvar_y]
  nlinarith [hvariance_bound]

end RegularityStructures

end
