/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian tail recurrences

The Gaussian Stein solution has polynomial tails when its datum has polynomial growth.  The
recurrence below is the analytic step used to prove that assertion; it is the usual integration
by parts recurrence for Gaussian moments.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace RegularityStructures

private lemma integrableOn_gaussian_nat_pow {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t ^ k * rexp (-t ^ 2 / 2)) (Ioi a) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 2) (s := (k : ℝ))
    (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith)
  have h' : IntegrableOn
      (fun t : ℝ => t ^ (k : ℝ) * rexp (-(1 / 2 : ℝ) * t ^ 2)) (Ioi a) :=
    h.mono_set (Ioi_subset_Ioi ha)
  convert h' using 1
  · funext t
    rw [Real.rpow_natCast]
    congr 2
    ring

private lemma tendsto_gaussian_nat_pow_exp {k : ℕ} :
    Tendsto (fun t : ℝ => t ^ k * rexp (-t ^ 2 / 2)) atTop (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) (k : ℝ)
  have h' : Tendsto (fun t : ℝ => |t| ^ k * rexp (-(1 / 2 : ℝ) * t ^ 2)) atTop (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop] at h
    refine (h.mono_left le_sup_right).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [abs_of_nonneg ht, Real.rpow_natCast]
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [abs_of_nonneg ht]
  ring_nf

theorem gaussian_tail_nat_pow_recurrence {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Ioi a, t ^ (k + 1) * rexp (-t ^ 2 / 2) =
      a ^ k * rexp (-a ^ 2 / 2) +
        (k : ℝ) * ∫ t in Ioi a, t ^ (k - 1) * rexp (-t ^ 2 / 2) := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.zero_add, Nat.zero_sub, Nat.cast_zero, zero_mul, add_zero, pow_zero]
    have hderiv : ∀ t ∈ Ici a,
        HasDerivAt (fun x : ℝ => -rexp (-x ^ 2 / 2))
          (t * rexp (-t ^ 2 / 2)) t := by
      intro t ht
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-t) t := by
        convert ((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ) using 1
        · norm_num
        · norm_num
          ring
      have hexp := (Real.hasDerivAt_exp _).comp t harg
      have hneg := hexp.neg
      convert hneg using 1
      · funext x
        dsimp
      · ring
    have hint : IntegrableOn
        (fun t : ℝ => t * rexp (-t ^ 2 / 2)) (Ioi a) := by
      simpa [pow_one] using (integrableOn_gaussian_nat_pow (k := 1) ha)
    have hinf : Tendsto (fun x : ℝ => -rexp (-x ^ 2 / 2)) atTop (𝓝 0) := by
      simpa using (tendsto_gaussian_nat_pow_exp (k := 0)).neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := a) (f := fun x : ℝ => -rexp (-x ^ 2 / 2))
      (f' := fun x : ℝ => x * rexp (-x ^ 2 / 2))
      hderiv hint hinf
    rw [show (fun t : ℝ => t ^ 1 * rexp (-t ^ 2 / 2)) =
      (fun t : ℝ => t * rexp (-t ^ 2 / 2)) by funext t; simp [pow_one]]
    simpa using h
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hu : ∀ t ∈ Ioi a, HasDerivAt (fun x : ℝ => x ^ k)
        ((k : ℝ) * t ^ (k - 1)) t := by
      intro t ht
      have h := (hasDerivAt_id t).pow k
      change HasDerivAt (id ^ k) ((k : ℝ) * t ^ (k - 1)) t
      simpa [Nat.cast_sub hkpos.le] using h
    have hv : ∀ t ∈ Ioi a, HasDerivAt (fun x : ℝ => -rexp (-x ^ 2 / 2))
        (t * rexp (-t ^ 2 / 2)) t := by
      intro t ht
      have harg : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-t) t := by
        convert ((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ) using 1
        · norm_num
        · norm_num
          ring
      have hexp := (Real.hasDerivAt_exp _).comp t harg
      have hneg := hexp.neg
      convert hneg using 1
      · funext x
        dsimp
      · ring
    have huv' : IntegrableOn
        ((fun t : ℝ => t ^ k) * (fun t : ℝ => t * rexp (-t ^ 2 / 2))) (Ioi a) := by
      convert integrableOn_gaussian_nat_pow (k := k + 1) ha using 1
      funext t
      simp only [Pi.mul_apply]
      ring
    have hu'v : IntegrableOn
        ((fun t : ℝ => (k : ℝ) * t ^ (k - 1)) *
          (fun t : ℝ => -rexp (-t ^ 2 / 2))) (Ioi a) := by
      have hbase := (integrableOn_gaussian_nat_pow (k := k - 1) ha).const_mul (-(k : ℝ))
      refine hbase.congr ?_
      filter_upwards [] with t
      simp only [Pi.mul_apply]
      ring
    have hzero : Tendsto ((fun t : ℝ => t ^ k) *
        (fun t : ℝ => -rexp (-t ^ 2 / 2))) (𝓝[>] a)
        (𝓝 (-a ^ k * rexp (-a ^ 2 / 2))) := by
      have hcont : ContinuousAt ((fun t : ℝ => t ^ k) *
          (fun t : ℝ => -rexp (-t ^ 2 / 2))) a := by
        fun_prop
      convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
      · simp [Pi.mul_apply]
    have hinfty : Tendsto ((fun t : ℝ => t ^ k) *
        (fun t : ℝ => -rexp (-t ^ 2 / 2))) atTop (𝓝 0) := by
      convert (tendsto_gaussian_nat_pow_exp (k := k)).neg using 1
      · funext x
        dsimp
        ring
      · simp
    have h := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := a) (u := fun t : ℝ => t ^ k) (u' := fun t : ℝ => (k : ℝ) * t ^ (k - 1))
      (v := fun t : ℝ => -rexp (-t ^ 2 / 2))
      (v' := fun t : ℝ => t * rexp (-t ^ 2 / 2)) hu hv huv' hu'v hzero hinfty
    have hleft : (∫ x in Ioi a, x ^ k * (x * rexp (-x ^ 2 / 2))) =
        ∫ x in Ioi a, x ^ (k + 1) * rexp (-x ^ 2 / 2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [pow_succ]
      ring
    have hright : (∫ x in Ioi a, (k : ℝ) * x ^ (k - 1) *
        -rexp (-x ^ 2 / 2)) =
        ∫ x in Ioi a, -(k : ℝ) * (x ^ (k - 1) * rexp (-x ^ 2 / 2)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [hleft, hright] at h
    have hneg_int : (∫ x in Ioi a, -(k : ℝ) *
        (x ^ (k - 1) * rexp (-x ^ 2 / 2))) =
        -∫ x in Ioi a, (k : ℝ) *
          (x ^ (k - 1) * rexp (-x ^ 2 / 2)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [hneg_int] at h
    have hrewrite : (∫ x in Ioi a, (k : ℝ) *
        (x ^ (k - 1) * rexp (-x ^ 2 / 2))) =
        (k : ℝ) * ∫ x in Ioi a, x ^ (k - 1) * rexp (-x ^ 2 / 2) := by
      rw [integral_const_mul]
    rw [hrewrite] at h
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h

theorem gaussian_tail_nat_pow_bound {k : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a →
      0 ≤ ∫ t in Ioi a, t ^ k * rexp (-t ^ 2 / 2) ∧
      ∫ t in Ioi a, t ^ k * rexp (-t ^ 2 / 2) ≤
        C * (1 + a ^ k) * rexp (-a ^ 2 / 2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k = 0
      · subst k
        refine ⟨2, by norm_num, ?_⟩
        intro a ha
        have hnonneg : 0 ≤ ∫ t in Ioi a, rexp (-t ^ 2 / 2) := by
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact le_of_lt (Real.exp_pos _)
        have hzero := gaussian_tail_nat_pow_recurrence (k := 0)
          (le_trans (by norm_num) ha)
        have htail1 : ∫ t in Ioi a, t * rexp (-t ^ 2 / 2) =
            rexp (-a ^ 2 / 2) := by simpa using hzero
        have hmono : ∫ t in Ioi a, rexp (-t ^ 2 / 2) ≤
            ∫ t in Ioi a, t * rexp (-t ^ 2 / 2) := by
          apply integral_mono_ae
          · simpa [IntegrableOn, pow_zero] using
              (integrableOn_gaussian_nat_pow (k := 0) (le_trans (by norm_num) ha))
          · simpa [IntegrableOn, pow_one] using
              (integrableOn_gaussian_nat_pow (k := 1) (le_trans (by norm_num) ha))
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have hta : a < t := ht
            have ht1 : 1 ≤ t := le_trans ha hta.le
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right ht1 (Real.exp_pos (-t ^ 2 / 2)).le
        constructor
        · simpa [pow_zero] using hnonneg
        · have hmono' : ∫ t in Ioi a, t ^ (0 : ℕ) * rexp (-t ^ 2 / 2) ≤
              ∫ t in Ioi a, t ^ (1 : ℕ) * rexp (-t ^ 2 / 2) := by
            simpa [pow_zero, pow_one] using hmono
          have htail1' : ∫ t in Ioi a, t ^ (1 : ℕ) * rexp (-t ^ 2 / 2) =
              rexp (-a ^ 2 / 2) := by simpa [pow_one] using htail1
          rw [htail1'] at hmono'
          have he : 0 ≤ rexp (-a ^ 2 / 2) := (Real.exp_pos _).le
          have hfactor : (1 : ℝ) ≤ 2 * (1 + a ^ (0 : ℕ)) := by norm_num
          calc
            ∫ t in Ioi a, t ^ (0 : ℕ) * rexp (-t ^ 2 / 2) ≤ rexp (-a ^ 2 / 2) := hmono'
            _ ≤ 2 * (1 + a ^ (0 : ℕ)) * rexp (-a ^ 2 / 2) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor he
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        have hjlt : j - 1 < j + 1 := by omega
        rcases ih (j - 1) (by omega) with ⟨C, hC, hbound⟩
        refine ⟨1 + (j : ℝ) * C, ?_, ?_⟩
        · positivity
        intro a ha
        have hrec := gaussian_tail_nat_pow_recurrence (k := j)
          (le_trans (by norm_num) ha)
        have hprev := hbound a ha
        have hpow : a ^ (j - 1) ≤ a ^ j := by
          exact pow_le_pow_right₀ ha (Nat.sub_le j 1)
        have hpoly : 1 + a ^ (j - 1) ≤ 1 + a ^ j := by
          simpa [add_comm] using add_le_add_left hpow 1
        have hnonneg : 0 ≤ ∫ t in Ioi a, t ^ (j + 1) * rexp (-t ^ 2 / 2) := by
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg
            (pow_nonneg (le_trans (le_trans (by norm_num) ha) ht.le) _)
            (Real.exp_pos _).le
        constructor
        · exact hnonneg
        · rw [hrec]
          have hmul := mul_le_mul_of_nonneg_left hprev.2 (by positivity : (0 : ℝ) ≤ j)
          have hmul' := mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ (j : ℝ) * C)
          have he : 0 ≤ rexp (-a ^ 2 / 2) := (Real.exp_pos _).le
          calc
            a ^ j * rexp (-a ^ 2 / 2) + (j : ℝ) *
                ∫ t in Ioi a, t ^ (j - 1) * rexp (-t ^ 2 / 2) ≤
                a ^ j * rexp (-a ^ 2 / 2) + (j : ℝ) *
                  (C * (1 + a ^ (j - 1)) * rexp (-a ^ 2 / 2)) :=
              add_le_add_right hmul (a ^ j * rexp (-a ^ 2 / 2))
            _ ≤ a ^ j * rexp (-a ^ 2 / 2) + (j : ℝ) *
                  (C * (1 + a ^ j) * rexp (-a ^ 2 / 2)) := by
              gcongr
            _ ≤ (1 + (j : ℝ) * C) * (1 + a ^ (j + 1)) *
                  rexp (-a ^ 2 / 2) := by
              have ha_pow : a ^ j ≤ 1 + a ^ (j + 1) := by
                have hpownext : a ^ j ≤ a ^ (j + 1) :=
                  pow_le_pow_right₀ ha (Nat.le_succ j)
                exact hpownext.trans
                  (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
              have hleft : a ^ j * rexp (-a ^ 2 / 2) ≤
                  (1 + a ^ (j + 1)) * rexp (-a ^ 2 / 2) := by
                exact mul_le_mul_of_nonneg_right ha_pow he
              have hright : (j : ℝ) *
                    (C * (1 + a ^ j) * rexp (-a ^ 2 / 2)) ≤
                  (j : ℝ) * C * (1 + a ^ (j + 1)) * rexp (-a ^ 2 / 2) := by
                have hpownext : a ^ j ≤ a ^ (j + 1) :=
                  pow_le_pow_right₀ ha (Nat.le_succ j)
                have hpoly' : 1 + a ^ j ≤ 1 + a ^ (j + 1) := by
                  simpa [add_comm] using add_le_add_left hpownext 1
                have hmul' := mul_le_mul_of_nonneg_left hpoly'
                  (mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j) hC)
                have hmul'' := mul_le_mul_of_nonneg_right hmul' he
                simpa [mul_assoc] using hmul''
              calc
                _ ≤ (1 + a ^ (j + 1)) * rexp (-a ^ 2 / 2) +
                    (j : ℝ) * C * (1 + a ^ (j + 1)) * rexp (-a ^ 2 / 2) :=
                  add_le_add hleft hright
                _ = _ := by ring

end RegularityStructures

end
