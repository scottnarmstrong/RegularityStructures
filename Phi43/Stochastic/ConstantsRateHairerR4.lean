/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.Order.Field.GeomSum
public import RegularityStructures.Analysis.Heat.Decomposition.Support

/-!
# Increments of Hairer's truncated kernel on `ℝ × ℝ³`

Each dyadic shell `(2ⁿ)³ K₀(S^{2ⁿ} ·)` of `hairerKernel N` is Lipschitz at its own scale; summing
over the finitely many shells that meet the point gives
`|K(w - η) - K(w)| ≤ B ‖η‖ ‖w‖⁻⁴` for `8‖η‖ ≤ ‖w‖` in the parabolic norm.
-/

@[expose] public noncomputable section

open Set

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem exists_lipschitz_annKernel0 (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : ParabolicSpace,
      |annKernel0C N a - annKernel0C N b| ≤
        L * (|a.1 - b.1| + ∑ i, |a.2 i - b.2 i|) := by
  have hsupport : HasCompactSupport (annKernel0C N) :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun z hz =>
      annKernel0C_eq_zero N (not_le.1 hz)
  obtain ⟨C, hC⟩ := (contDiff_annKernel0C N).lipschitzWith_of_hasCompactSupport hsupport
    (by simp)
  refine ⟨C, C.2, fun a b => ?_⟩
  have h1 := hC.dist_le_mul a b
  rw [Real.dist_eq] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
  rw [Prod.dist_eq]
  apply max_le
  · rw [Real.dist_eq]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => abs_nonneg _)
  · rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq]
    exact le_add_of_nonneg_of_le (abs_nonneg _)
      (Finset.single_le_sum (f := fun j => |a.2 j - b.2 j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))

private theorem shell_increment_le (N n : ℕ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a b : ParabolicSpace, |annKernel0C N a - annKernel0C N b| ≤
      L * (|a.1 - b.1| + ∑ i, |a.2 i - b.2 i|))
    (w η : ParabolicSpace) (hp : (2 : ℝ) ^ n * parabolicNorm η ≤ 1) :
    |annShellC N n (w - η) - annShellC N n w| ≤ 2 * L * 16 ^ n * parabolicNorm η := by
  set c : ℝ := (2 : ℝ) ^ n with hc
  have hc0 : 0 < c := by positivity
  set p : ℝ := parabolicNorm η with hpdef
  have hp0 : 0 ≤ p := parabolicNorm_nonneg η
  have hdil : parabolicDilate c (w - η) = parabolicDilate c w - parabolicDilate c η := by
    apply Prod.ext
    · simp [parabolicDilate]
      ring
    · funext i
      simp [parabolicDilate]
      ring
  have hshell : ∀ z, annShellC N n z = c ^ 3 * annKernel0C N (parabolicDilate c z) :=
    fun z => rfl
  rw [hshell, hshell, hdil, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have h1 := hL (parabolicDilate c w - parabolicDilate c η) (parabolicDilate c w)
  have h2 : |(parabolicDilate c w - parabolicDilate c η).1 - (parabolicDilate c w).1| +
      ∑ i, |(parabolicDilate c w - parabolicDilate c η).2 i - (parabolicDilate c w).2 i| =
      c ^ 2 * |η.1| + c * ∑ i, |η.2 i| := by
    have e1 : (parabolicDilate c w - parabolicDilate c η).1 - (parabolicDilate c w).1 =
        -(c ^ 2 * η.1) := by simp [parabolicDilate]
    have e2 : ∀ i, (parabolicDilate c w - parabolicDilate c η).2 i -
        (parabolicDilate c w).2 i = -(c * η.2 i) := by
      intro i
      simp [parabolicDilate]
    simp_rw [e1, e2, abs_neg, abs_mul, abs_of_nonneg hc0.le, abs_of_nonneg (sq_nonneg c)]
    rw [← Finset.mul_sum]
  rw [h2] at h1
  have hsq : |η.1| ≤ p ^ 2 := by
    have hs : Real.sqrt |η.1| ≤ p := by
      rw [hpdef]
      unfold parabolicNorm
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => abs_nonneg _)
    calc
      |η.1| = Real.sqrt |η.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ p ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  have hsum : ∑ i, |η.2 i| ≤ p := by
    rw [hpdef]
    unfold parabolicNorm
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hcp : c * p ≤ 1 := hp
  have hA : c ^ 2 * |η.1| ≤ c * p := by
    calc
      c ^ 2 * |η.1| ≤ c ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg c)
      _ = (c * p) * (c * p) := by ring
      _ ≤ (c * p) * 1 := mul_le_mul_of_nonneg_left hcp (by positivity)
      _ = c * p := mul_one _
  have hB : c * ∑ i, |η.2 i| ≤ c * p := mul_le_mul_of_nonneg_left hsum hc0.le
  have hfin : |annKernel0C N (parabolicDilate c w - parabolicDilate c η) -
      annKernel0C N (parabolicDilate c w)| ≤ L * (2 * (c * p)) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hL0)
  have h16 : (16 : ℝ) ^ n = c ^ 4 := by
    rw [hc, ← pow_mul, mul_comm, pow_mul]
    norm_num
  calc
    c ^ 3 * |annKernel0C N (parabolicDilate c w - parabolicDilate c η) -
        annKernel0C N (parabolicDilate c w)| ≤ c ^ 3 * (L * (2 * (c * p))) :=
      mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 2 * L * 16 ^ n * p := by rw [h16]; ring

private theorem geom_sum_sixteen_le {X : ℝ} (M : ℕ) (hM : ∀ n < M, (2 : ℝ) ^ n ≤ X) :
    ∑ n ∈ Finset.range M, (16 : ℝ) ^ n ≤ 16 / 15 * X ^ 4 := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    have hX := hM m (by omega)
    have hgeom : ∑ n ∈ Finset.range (m + 1), (16 : ℝ) ^ n = ((16 : ℝ) ^ (m + 1) - 1) / 15 := by
      rw [geom_sum_eq (by norm_num)]
      norm_num
    rw [hgeom]
    have h2 : (16 : ℝ) ^ (m + 1) = 16 * ((2 : ℝ) ^ m) ^ 4 := by
      rw [← pow_mul, pow_succ]
      have : (16 : ℝ) ^ m = 2 ^ (m * 4) := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm]
      rw [this]
      ring
    have h3 : ((2 : ℝ) ^ m) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by positivity) hX 4
    rw [h2]
    linarith

theorem constantsRate_hairerKernel_increment (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w η : ParabolicSpace, 0 < parabolicNorm w →
      8 * parabolicNorm η ≤ parabolicNorm w →
      |hairerKernel N (w - η) - hairerKernel N w| ≤
        B * parabolicNorm η * parabolicNorm w ^ (-(4 : ℝ)) := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_annKernel0 N
  refine ⟨2 * L * (16 / 15) * (8 / 7) ^ 4, by positivity, ?_⟩
  intro w η hw hη
  set u : ℝ := parabolicNorm w with hu
  set p : ℝ := parabolicNorm η with hpdef
  have hp0 : 0 ≤ p := parabolicNorm_nonneg η
  have hlow : 7 * u / 8 ≤ parabolicNorm (w - η) := by
    have h := parabolicNorm_add_le (w - η) η
    rw [sub_add_cancel] at h
    linarith
  have hex : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < 7 * u / 8 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  classical
  let M : ℕ := Nat.find hex
  have hM : (2 : ℝ)⁻¹ ^ M < 7 * u / 8 := Nat.find_spec hex
  have hvan : ∀ n, M ≤ n → annShellC N n w = 0 ∧ annShellC N n (w - η) = 0 := by
    intro n hn
    have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ M :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hn
    exact ⟨annShellC_eq_zero (by linarith), annShellC_eq_zero (by linarith)⟩
  have hrel : ∀ n < M, (2 : ℝ) ^ n ≤ 8 / (7 * u) := by
    intro n hn
    have hnot : ¬ (2 : ℝ)⁻¹ ^ n < 7 * u / 8 := Nat.find_min hex hn
    have hge : 7 * u / 8 ≤ (2 : ℝ)⁻¹ ^ n := le_of_not_gt hnot
    rw [inv_pow] at hge
    rw [le_div_iff₀ (by positivity)]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_inv_comm₀ (by positivity) h2n] at hge
    have := hge
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  have hsum1 : hairerKernel N (w - η) = ∑ n ∈ Finset.range M, annShellC N n (w - η) := by
    unfold hairerKernel
    apply tsum_eq_sum
    intro n hn
    exact (hvan n (not_lt.mp (by simpa using hn))).2
  have hsum2 : hairerKernel N w = ∑ n ∈ Finset.range M, annShellC N n w := by
    unfold hairerKernel
    apply tsum_eq_sum
    intro n hn
    exact (hvan n (not_lt.mp (by simpa using hn))).1
  rw [hsum1, hsum2, ← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range M,
      |annShellC N n (w - η) - annShellC N n w| ≤ 2 * L * 16 ^ n * p := by
    intro n hn
    have hn' : n < M := Finset.mem_range.mp hn
    apply shell_increment_le N n hL0 hL
    have h1 := hrel n hn'
    have h2 : (2 : ℝ) ^ n * p ≤ 8 / (7 * u) * (u / 8) :=
      mul_le_mul h1 (by linarith) hp0 (by positivity)
    have h3 : 8 / (7 * u) * (u / 8) = 1 / 7 := by field_simp
    linarith
  calc
    |∑ n ∈ Finset.range M, (annShellC N n (w - η) - annShellC N n w)| ≤
        ∑ n ∈ Finset.range M, |annShellC N n (w - η) - annShellC N n w| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le (Finset.range M) (fun n => annShellC N n (w - η) - annShellC N n w)
    _ ≤ ∑ n ∈ Finset.range M, 2 * L * 16 ^ n * p := Finset.sum_le_sum hterm
    _ = 2 * L * p * ∑ n ∈ Finset.range M, (16 : ℝ) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ 2 * L * p * (16 / 15 * (8 / (7 * u)) ^ 4) :=
      mul_le_mul_of_nonneg_left (geom_sum_sixteen_le M hrel) (by positivity)
    _ = 2 * L * (16 / 15) * (8 / 7) ^ 4 * p * u ^ (-(4 : ℝ)) := by
      rw [Real.rpow_neg hw.le]
      have : u ^ (4 : ℝ) = u ^ 4 := by exact_mod_cast Real.rpow_natCast u 4
      rw [this]
      field_simp

end RegularityStructures.Phi43

end
