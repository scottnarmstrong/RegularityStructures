/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.MeanInequalities

/-!
# Moment tools for the parallel Pi half

Three elementary tools on a probability space, for `ℝ≥0∞`-valued random variables:

* `piHalf_lintegral_pow_le_of_le`: a moment of order `q` controls the moments of order `m ≤ q`;
* `piHalf_lintegral_mul_pow_le`: the Cauchy-Schwarz estimate `E (a b)^p ≤ A^p B^p` from
  moments of order `2 p`;
* `piHalf_finset_sum_pow_le`: the finite-sum power inequality.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- Lyapunov: a bound on the `q`-th moment gives the same bound on every lower integer moment. -/
theorem piHalf_lintegral_pow_le_of_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g P) {m q : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q) {B : ℝ}
    (h : ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal B ^ q) :
    ∫⁻ ω, ‖g ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal B ^ m := by
  have hq : 1 ≤ q := hm.trans hmq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hle := eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (f := g)
    (p := (m : ℝ≥0∞)) (q := (q : ℝ≥0∞)) (by exact_mod_cast hmq)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hm.trans_lt' Nat.zero_lt_one |>.ne')
      (by simp) hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using (hq.trans_lt' Nat.zero_lt_one).ne')
      (by simp) hg] at hle
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at hle
  have hq' : (∫⁻ ω, ‖g ω‖ₑ ^ q ∂P) ^ (1 / (q : ℝ)) ≤ ENNReal.ofReal B := by
    calc (∫⁻ ω, ‖g ω‖ₑ ^ q ∂P) ^ (1 / (q : ℝ))
        ≤ (ENNReal.ofReal B ^ q) ^ (1 / (q : ℝ)) :=
          ENNReal.rpow_le_rpow h (by positivity)
      _ = ENNReal.ofReal B := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          field_simp
          simp
  have h2 := hle.trans hq'
  have h3 := ENNReal.rpow_le_rpow h2 hmpos.le
  rw [← ENNReal.rpow_mul] at h3
  have : 1 / (m : ℝ) * (m : ℝ) = 1 := by field_simp
  rw [this, ENNReal.rpow_one, ENNReal.rpow_natCast] at h3
  exact h3

/-- Cauchy-Schwarz for moments: `E (a b)^p ≤ A^p B^p` from `E a^(2p) ≤ A^(2p)`,
`E b^(2p) ≤ B^(2p)`. -/
theorem piHalf_lintegral_mul_pow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a b : Ω → ℝ≥0∞} (ha : AEMeasurable a P) (hb : AEMeasurable b P) {p : ℕ} {A B : ℝ}
    (hA : ∫⁻ ω, a ω ^ (2 * p) ∂P ≤ ENNReal.ofReal A ^ (2 * p))
    (hB : ∫⁻ ω, b ω ^ (2 * p) ∂P ≤ ENNReal.ofReal B ^ (2 * p)) :
    ∫⁻ ω, (a ω * b ω) ^ p ∂P ≤ ENNReal.ofReal A ^ p * ENNReal.ofReal B ^ p := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := fun ω => a ω ^ p) (g := fun ω => b ω ^ p) (ha.pow_const p) (hb.pow_const p)
  have key : ∀ (c : Ω → ℝ≥0∞) (C : ℝ), ∫⁻ ω, c ω ^ (2 * p) ∂P ≤ ENNReal.ofReal C ^ (2 * p) →
      (∫⁻ ω, (c ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal C ^ p := by
    intro c C hC
    have e : ∀ ω, (c ω ^ p) ^ (2 : ℝ) = c ω ^ (2 * p) := fun ω => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← pow_mul, mul_comm]
    simp_rw [e]
    calc (∫⁻ ω, c ω ^ (2 * p) ∂P) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal C ^ (2 * p)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hC (by norm_num)
      _ = ENNReal.ofReal C ^ p := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          push_cast
          rw [show (2 : ℝ) * p * (1 / 2) = p by ring, ENNReal.rpow_natCast]
  calc ∫⁻ ω, (a ω * b ω) ^ p ∂P
      = ∫⁻ ω, (fun ω => a ω ^ p) ω * (fun ω => b ω ^ p) ω ∂P := by
        simp_rw [mul_pow]
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul' (key a A hA) (key b B hB)

/-- The finite-sum power inequality `(∑ f)^p ≤ card^(p-1) ∑ f^p`. -/
theorem piHalf_finset_sum_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℕ}
    (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (s.card : ℝ≥0∞) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow s f (p := (p : ℝ)) (by exact_mod_cast hp)
  have e : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp]; simp
  rw [e] at h
  simpa only [ENNReal.rpow_natCast] using h

end RegularityStructures

end
