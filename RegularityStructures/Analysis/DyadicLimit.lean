/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits from a dyadic Cauchy bound

If `|φ s - φ u| ≤ L s^β` whenever `s / 2 ≤ u ≤ s ≤ S` (`β > 0`), then `φ` has a limit `φ₀` as
`s ↓ 0` and `|φ s - φ₀| ≤ 2 L / (1 - 2^{-β}) s^β`. This is the dyadic summation used in the proof
of [Hos25, Theorem 4.1] (arXiv:2310.07396v2).
-/

public section

open Filter Set
open scoped Topology

namespace RegularityStructures

section

variable {φ : ℝ → ℝ} {S L β : ℝ}

private lemma theta_lt_one (hβ : 0 < β) : (2 : ℝ) ^ (-β) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

private lemma half_rpow {s : ℝ} (hs : 0 < s) : (s / 2) ^ β = s ^ β * (2 : ℝ) ^ (-β) := by
  rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]

private lemma dyadic_chain (hβ : 0 < β)
    (h : ∀ s u, 0 < s → s ≤ S → s / 2 ≤ u → u ≤ s → |φ s - φ u| ≤ L * s ^ β) (n : ℕ) :
    ∀ s, 0 < s → s ≤ S →
      |φ s - φ (s / 2 ^ n)| ≤
        L * s ^ β * ((1 - ((2 : ℝ) ^ (-β)) ^ n) / (1 - 2 ^ (-β))) := by
  have hθ := theta_lt_one hβ
  have hθ0 : 0 < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : 0 < 1 - (2 : ℝ) ^ (-β) := by linarith
  induction n with
  | zero => intro s hs _; simp
  | succ n ih =>
    intro s hs hsS
    have hs2 : 0 < s / 2 := by positivity
    have e : s / 2 ^ (n + 1) = (s / 2) / 2 ^ n := by rw [pow_succ]; field_simp
    have h2 := ih (s / 2) hs2 (by linarith)
    have h3 := h s (s / 2) hs hsS le_rfl (by linarith)
    rw [half_rpow hs] at h2
    rw [e]
    set θ := (2 : ℝ) ^ (-β)
    set a := s ^ β
    have hq : 0 ≤ (1 - θ ^ n) / (1 - θ) :=
      div_nonneg (by linarith [pow_le_one₀ hθ0.le hθ.le (n := n)]) h1.le
    have key : L * a * ((1 - θ ^ (n + 1)) / (1 - θ)) =
        L * a + L * (a * θ) * ((1 - θ ^ n) / (1 - θ)) := by
      field_simp; ring
    calc |φ s - φ (s / 2 / 2 ^ n)|
        = |(φ s - φ (s / 2)) + (φ (s / 2) - φ (s / 2 / 2 ^ n))| := by ring_nf
      _ ≤ |φ s - φ (s / 2)| + |φ (s / 2) - φ (s / 2 / 2 ^ n)| := abs_add_le _ _
      _ ≤ _ := by rw [key]; linarith

private lemma abs_sub_le_aux (hβ : 0 < β) (hL : 0 ≤ L)
    (h : ∀ s u, 0 < s → s ≤ S → s / 2 ≤ u → u ≤ s → |φ s - φ u| ≤ L * s ^ β) :
    ∀ s u, 0 < u → u ≤ s → s ≤ S →
      |φ s - φ u| ≤ 2 * L / (1 - 2 ^ (-β)) * s ^ β := by
  intro s u hu hus hsS
  have hs : 0 < s := hu.trans_le hus
  have hθ := theta_lt_one hβ
  have hθ0 : 0 < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : 0 < 1 - (2 : ℝ) ^ (-β) := by linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := s / u) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hu]; linarith) (by norm_num)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2n1 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [le_div_iff₀ hu] at hn1
  rw [div_lt_iff₀ hu] at hn2
  have hv : s / 2 ^ n ≤ S := by
    calc s / 2 ^ n ≤ s := div_le_self hs.le (one_le_pow₀ (by norm_num))
      _ ≤ S := hsS
  have hvpos : 0 < s / 2 ^ n := by positivity
  have hu1 : u ≤ s / 2 ^ n := by rw [le_div_iff₀ h2n]; linarith
  have hu2 : s / 2 ^ n / 2 ≤ u := by
    rw [div_div, ← pow_succ, div_le_iff₀ h2n1]; linarith
  have c1 := dyadic_chain hβ h n s hs hsS
  have c2 := h (s / 2 ^ n) u hvpos hv hu2 hu1
  have hvs : (s / 2 ^ n) ^ β ≤ s ^ β :=
    Real.rpow_le_rpow hvpos.le (div_le_self hs.le (one_le_pow₀ (by norm_num))) hβ.le
  have hq : (1 - ((2 : ℝ) ^ (-β)) ^ n) / (1 - 2 ^ (-β)) ≤ 1 / (1 - 2 ^ (-β)) :=
    div_le_div_of_nonneg_right (by linarith [pow_nonneg hθ0.le n]) h1.le
  have hq1 : 1 ≤ 1 / (1 - (2 : ℝ) ^ (-β)) := by
    rw [le_div_iff₀ h1]; linarith
  have hsb : 0 ≤ s ^ β := Real.rpow_nonneg hs.le _
  have e : 2 * L / (1 - 2 ^ (-β)) * s ^ β = L * s ^ β * (1 / (1 - 2 ^ (-β))) +
      L * s ^ β * (1 / (1 - 2 ^ (-β))) := by ring
  calc |φ s - φ u|
      = |(φ s - φ (s / 2 ^ n)) + (φ (s / 2 ^ n) - φ u)| := by ring_nf
    _ ≤ |φ s - φ (s / 2 ^ n)| + |φ (s / 2 ^ n) - φ u| := abs_add_le _ _
    _ ≤ L * s ^ β * (1 / (1 - 2 ^ (-β))) + L * s ^ β := by
        gcongr
        exact c1.trans (mul_le_mul_of_nonneg_left hq (mul_nonneg hL hsb))
        exact c2.trans (mul_le_mul_of_nonneg_left hvs hL)
    _ ≤ _ := by
        rw [e]
        have : L * s ^ β ≤ L * s ^ β * (1 / (1 - 2 ^ (-β))) :=
          le_mul_of_one_le_right (mul_nonneg hL hsb) hq1
        linarith

end

variable {φ : ℝ → ℝ} {S L β : ℝ}

theorem abs_sub_le_of_dyadic_bound (_hS : 0 < S) (hβ : 0 < β) (hL : 0 ≤ L)
    (h : ∀ s u, 0 < s → s ≤ S → s / 2 ≤ u → u ≤ s → |φ s - φ u| ≤ L * s ^ β) :
    ∀ s u, 0 < u → u ≤ s → s ≤ S →
      |φ s - φ u| ≤ 2 * L / (1 - 2 ^ (-β)) * s ^ β :=
  abs_sub_le_aux hβ hL h

theorem exists_tendsto_of_dyadic_bound (hS : 0 < S) (hβ : 0 < β) (hL : 0 ≤ L)
    (h : ∀ s u, 0 < s → s ≤ S → s / 2 ≤ u → u ≤ s → |φ s - φ u| ≤ L * s ^ β) :
    ∃ φ₀, Tendsto φ (𝓝[>] 0) (𝓝 φ₀) ∧
      ∀ s, 0 < s → s ≤ S → |φ s - φ₀| ≤ 2 * L / (1 - 2 ^ (-β)) * s ^ β := by
  have hθ := theta_lt_one hβ
  have h1 : 0 < 1 - (2 : ℝ) ^ (-β) := by linarith
  set c := 2 * L / (1 - (2 : ℝ) ^ (-β)) with hc
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg zero_le_two hL) h1.le
  have hb := abs_sub_le_aux hβ hL h
  set a : ℕ → ℝ := fun n => φ (S / 2 ^ n) with ha
  have hpos : ∀ n : ℕ, 0 < S / 2 ^ n := fun n => by positivity
  have hle : ∀ n : ℕ, S / 2 ^ n ≤ S := fun n =>
    div_le_self hS.le (one_le_pow₀ (by norm_num))
  have hanti : Antitone fun n : ℕ => S / 2 ^ n := fun m n hmn =>
    div_le_div_of_nonneg_left hS.le (by positivity) (pow_le_pow_right₀ (by norm_num) hmn)
  -- the bound for the geometric sequence
  have hg : Tendsto (fun n : ℕ => c * (S / 2 ^ n) ^ β) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => S / 2 ^ n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul S
    have h0 : Tendsto (fun x : ℝ => c * x ^ β) (𝓝 0) (𝓝 (c * 0 ^ β)) :=
      ((Real.continuous_rpow_const hβ.le).const_mul c).tendsto 0
    rw [Real.zero_rpow hβ.ne', mul_zero] at h0
    exact h0.comp this
  have hT : Tendsto (fun n : ℕ => S / 2 ^ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, ← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul S
  have hab : ∀ n m N : ℕ, N ≤ n → N ≤ m → dist (a n) (a m) ≤ c * (S / 2 ^ N) ^ β := by
    intro n m N hn hm
    have key : ∀ n m : ℕ, n ≤ m → N ≤ n → |a n - a m| ≤ c * (S / 2 ^ N) ^ β := by
      intro n m hnm hNn
      refine (hb _ _ (hpos m) (hanti hnm) (hle n)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hpos n).le (hanti hNn) hβ.le) hc0
    rw [Real.dist_eq]
    rcases le_total n m with h' | h'
    · exact key n m h' hn
    · rw [abs_sub_comm]; exact key m n h' hm
  have hcs : CauchySeq a := cauchySeq_of_le_tendsto_0 _ hab hg
  obtain ⟨φ₀, hφ₀⟩ := cauchySeq_tendsto_of_complete hcs
  have hbound : ∀ s, 0 < s → s ≤ S → |φ s - φ₀| ≤ c * s ^ β := by
    intro s hs hsS
    have hlim : Tendsto (fun n => |φ s - a n|) atTop (𝓝 |φ s - φ₀|) :=
      (tendsto_const_nhds.sub hφ₀).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [hT.eventually (ge_mem_nhds hs)] with n hn
    exact hb s _ (hpos n) hn hsS
  refine ⟨φ₀, ?_, hbound⟩
  have h0 : Tendsto (fun x : ℝ => c * x ^ β) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const hβ.le).const_mul c).tendsto 0
    rw [Real.zero_rpow hβ.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ h0)
  filter_upwards [Ioc_mem_nhdsGT hS] with s hs
  rw [Real.dist_eq]
  exact hbound s hs.1 hs.2

end RegularityStructures

end
