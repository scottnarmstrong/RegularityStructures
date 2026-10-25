/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# Increment bound for the Euclidean Hairer kernel

For `K_N = ∑ₙ annShellC N n` we prove `|K_N (z + h) - K_N z| ≲ ‖h‖ ‖z‖⁻⁴` for `‖h‖ ≤ ‖z‖ / 2`
(parabolic sizes).  The proof is shellwise: the base profile `annKernel0C N` is Lipschitz in the
parabolic metric (a time increment `τ` costs `|τ| ≤ ‖k‖² ≤ ‖k‖` for `‖k‖ ≤ 1`), the `n`-th shell
therefore changes by `≲ 16ⁿ ‖h‖`, and only the shells with `2⁻ⁿ ≳ ‖z‖` contribute.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem kinc_exists_abs_le (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ParabolicSpace, |annKernel0C N z| ≤ B := by
  have hsupport : HasCompactSupport (annKernel0C N) :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun z hz =>
      annKernel0C_eq_zero N (not_le.1 hz)
  obtain ⟨B, hB⟩ := (contDiff_annKernel0C N).continuous.abs.bounded_above_of_compact_support
    (hsupport.norm)
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro z
  have hz := (hB z).trans (le_max_left B 0)
  simpa only [Real.norm_eq_abs, abs_abs] using hz

private theorem kinc_norm_le_parabolicNorm {k : ParabolicSpace} (hk : parabolicNorm k ≤ 1) :
    ‖k‖ ≤ parabolicNorm k := by
  have hs0 := Real.sqrt_nonneg |k.1|
  have hsum : ∀ i, |k.2 i| ≤ ∑ j, |k.2 j| := fun i =>
    Finset.single_le_sum (f := fun j => |k.2 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ j, |k.2 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hs1 : √|k.1| ≤ 1 := by unfold parabolicNorm at hk; linarith
  rw [Prod.norm_def, max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    have h1 : |k.1| = √|k.1| * √|k.1| := (Real.mul_self_sqrt (abs_nonneg _)).symm
    have h2 : √|k.1| * √|k.1| ≤ √|k.1| * 1 := mul_le_mul_of_nonneg_left hs1 hs0
    unfold parabolicNorm
    linarith
  · rw [pi_norm_le_iff_of_nonneg (by unfold parabolicNorm; linarith)]
    intro i
    rw [Real.norm_eq_abs]
    unfold parabolicNorm
    linarith [hsum i]

/-- The base profile is Lipschitz in the parabolic size. -/
theorem annKernel0C_sub_abs_le (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w k : ParabolicSpace,
      |annKernel0C N (w + k) - annKernel0C N w| ≤ L * parabolicNorm k := by
  have hsupport : HasCompactSupport (annKernel0C N) :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun z hz =>
      annKernel0C_eq_zero N (not_le.1 hz)
  obtain ⟨K, hK⟩ := (contDiff_annKernel0C N).lipschitzWith_of_hasCompactSupport hsupport
    (by simp)
  obtain ⟨B, hB, hBd⟩ := kinc_exists_abs_le N
  refine ⟨max (K : ℝ) (2 * B), le_trans (by positivity) (le_max_right _ _), ?_⟩
  intro w k
  have hk0 := parabolicNorm_nonneg k
  by_cases hk : parabolicNorm k ≤ 1
  · have h1 := hK.dist_le_mul (w + k) w
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1
    have h2 := kinc_norm_le_parabolicNorm hk
    calc |annKernel0C N (w + k) - annKernel0C N w| ≤ K * ‖k‖ := h1
      _ ≤ K * parabolicNorm k := mul_le_mul_of_nonneg_left h2 K.2
      _ ≤ max (K : ℝ) (2 * B) * parabolicNorm k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
  · have hk1 : 1 ≤ parabolicNorm k := (not_le.1 hk).le
    have h1 : |annKernel0C N (w + k) - annKernel0C N w| ≤ 2 * B := by
      have := abs_sub (annKernel0C N (w + k)) (annKernel0C N w)
      linarith [hBd (w + k), hBd w]
    calc |annKernel0C N (w + k) - annKernel0C N w| ≤ 2 * B := h1
      _ ≤ 2 * B * parabolicNorm k := le_mul_of_one_le_right (by positivity) hk1
      _ ≤ max (K : ℝ) (2 * B) * parabolicNorm k :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hk0

private theorem kinc_dilate_add (c : ℝ) (z h : ParabolicSpace) :
    parabolicDilate c (z + h) = parabolicDilate c z + parabolicDilate c h := by
  simp [parabolicDilate, mul_add, smul_add]

private theorem kinc_two_pow_four (n : ℕ) : ((2 : ℝ) ^ n) ^ 3 * (2 : ℝ) ^ n = (16 : ℝ) ^ n := by
  rw [← pow_succ, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- Increment of a single dyadic shell. -/
theorem annShellC_sub_abs_le (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (n : ℕ) (z h : ParabolicSpace),
      |annShellC N n (z + h) - annShellC N n z| ≤ L * (16 : ℝ) ^ n * parabolicNorm h := by
  obtain ⟨L, hL, hLip⟩ := annKernel0C_sub_abs_le N
  refine ⟨L, hL, fun n z h => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h1 := hLip (parabolicDilate (2 ^ n) z) (parabolicDilate (2 ^ n) h)
  rw [parabolicNorm_parabolicDilate hc.le] at h1
  have e : annShellC N n (z + h) - annShellC N n z =
      ((2 : ℝ) ^ n) ^ 3 * (annKernel0C N (parabolicDilate (2 ^ n) (z + h)) -
        annKernel0C N (parabolicDilate (2 ^ n) z)) := by
    simp only [annShellC, scaledShell]
    ring
  rw [e, kinc_dilate_add, abs_mul, abs_of_nonneg (by positivity)]
  calc ((2 : ℝ) ^ n) ^ 3 * |annKernel0C N (parabolicDilate (2 ^ n) z +
          parabolicDilate (2 ^ n) h) - annKernel0C N (parabolicDilate (2 ^ n) z)|
      ≤ ((2 : ℝ) ^ n) ^ 3 * (L * (2 ^ n * parabolicNorm h)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = L * (((2 : ℝ) ^ n) ^ 3 * (2 : ℝ) ^ n) * parabolicNorm h := by ring
    _ = L * (16 : ℝ) ^ n * parabolicNorm h := by rw [kinc_two_pow_four]

private theorem kinc_exists_index {r : ℝ} (hr : 0 < r) :
    ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < r ∧ ∀ j < m, r ≤ (2 : ℝ)⁻¹ ^ j := by
  have hex : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < r := exists_pow_lt_of_lt_one hr (by norm_num)
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_⟩
  exact not_lt.1 (Nat.find_min hex hj)

private theorem kinc_geom_le (m : ℕ) : (∑ n ∈ Finset.range (m + 1), (16 : ℝ) ^ n) ≤
    2 * (16 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ 16 ^ m := by positivity
    calc (∑ n ∈ Finset.range (m + 1), (16 : ℝ) ^ n) + 16 ^ (m + 1)
        ≤ 2 * 16 ^ m + 16 ^ (m + 1) := by linarith
      _ ≤ 2 * 16 ^ (m + 1) := by rw [pow_succ]; linarith

private theorem kinc_sum_le {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : ∀ j < m, r ≤ (2 : ℝ)⁻¹ ^ j) :
    (∑ n ∈ Finset.range m, (16 : ℝ) ^ n) ≤ 2 * (r ^ 4)⁻¹ := by
  cases m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ j =>
    have h1 : r ≤ (2 : ℝ)⁻¹ ^ j := hm j (Nat.lt_succ_self j)
    have h2 : (2 : ℝ) ^ j ≤ r⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hr, ← inv_pow]
      exact h1
    have h3 : ((2 : ℝ) ^ j) ^ 4 ≤ (r⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
    have h4 : (16 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 4 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (∑ n ∈ Finset.range (j + 1), (16 : ℝ) ^ n) ≤ 2 * (16 : ℝ) ^ j := kinc_geom_le j
      _ ≤ 2 * (r⁻¹) ^ 4 := by rw [h4]; linarith
      _ = 2 * (r ^ 4)⁻¹ := by rw [inv_pow]

/-- The increment bound with the ratio `9/10` in place of `1/2`. -/
theorem hairerKernel_sub_abs_le_of_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z h : ParabolicSpace}, 0 < parabolicNorm z →
      parabolicNorm h ≤ 9 / 10 * parabolicNorm z →
        |hairerKernel N (z + h) - hairerKernel N z| ≤
          C * parabolicNorm h * parabolicNorm z ^ (-(4 : ℝ)) := by
  obtain ⟨L, hL, hshell⟩ := annShellC_sub_abs_le N
  refine ⟨20000 * L, by positivity, ?_⟩
  intro z h hz hh
  have hh0 := parabolicNorm_nonneg h
  set r : ℝ := parabolicNorm z / 10 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨m, hm1, hm2⟩ := kinc_exists_index hr0
  have hzh : r ≤ parabolicNorm (z + h) := by
    have := parabolicNorm_add_le (z + h) (-h)
    rw [add_neg_cancel_right, parabolicNorm_neg] at this
    rw [hr]; linarith
  have hvan : ∀ n, m ≤ n → annShellC N n z = 0 ∧ annShellC N n (z + h) = 0 := by
    intro n hn
    have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hn
    exact ⟨annShellC_eq_zero (hpow.trans_lt (hm1.trans (by rw [hr]; linarith))),
      annShellC_eq_zero (hpow.trans_lt (lt_of_lt_of_le hm1 hzh))⟩
  have hdiff : hairerKernel N (z + h) - hairerKernel N z =
      ∑ n ∈ Finset.range m, (annShellC N n (z + h) - annShellC N n z) := by
    have e1 : hairerKernel N (z + h) = ∑ n ∈ Finset.range m, annShellC N n (z + h) := by
      unfold hairerKernel
      exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).2
    have e2 : hairerKernel N z = ∑ n ∈ Finset.range m, annShellC N n z := by
      unfold hairerKernel
      exact tsum_eq_sum fun n hn => (hvan n (not_lt.1 (by simpa using hn))).1
    rw [e1, e2, Finset.sum_sub_distrib]
  have hpow : parabolicNorm z ^ (-(4 : ℝ)) = (parabolicNorm z ^ 4)⁻¹ := by
    rw [Real.rpow_neg hz.le]
    norm_cast
  have hrpow : (r ^ 4)⁻¹ = 10000 * (parabolicNorm z ^ 4)⁻¹ := by
    rw [hr, div_pow, inv_div]
    field_simp
    norm_num
  calc |hairerKernel N (z + h) - hairerKernel N z|
      ≤ ∑ n ∈ Finset.range m, |annShellC N n (z + h) - annShellC N n z| := by
        rw [hdiff]
        simpa only [Real.norm_eq_abs] using
          norm_sum_le (Finset.range m) (fun n => annShellC N n (z + h) - annShellC N n z)
    _ ≤ ∑ n ∈ Finset.range m, L * parabolicNorm h * (16 : ℝ) ^ n :=
        Finset.sum_le_sum fun n _ => by
          have := hshell n z h
          linarith [this, show L * (16 : ℝ) ^ n * parabolicNorm h =
            L * parabolicNorm h * (16 : ℝ) ^ n by ring]
    _ = L * parabolicNorm h * ∑ n ∈ Finset.range m, (16 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ L * parabolicNorm h * (2 * (r ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left (kinc_sum_le hr0 hm2) (by positivity)
    _ = 20000 * L * parabolicNorm h * parabolicNorm z ^ (-(4 : ℝ)) := by
        rw [hrpow, hpow]; ring

end RegularityStructures.Phi43

end
