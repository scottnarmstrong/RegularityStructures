/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Reflect
public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorWord
import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing

/-!
# Small scales: derivative shells centred at `x`, local order with polynomial growth

Growth version of the pairing bound for the shells `K_n` in the Taylor regime: the test
function lives in the ball of radius `2^{-n} ≤ 1`, so `C` is replaced by `2^q C`.
Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.19.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem tendsto_and_abs_pairing_word_scaledShell_le_growth {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x : ParabolicSpace} {γ C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C q) (ℓ : List (Fin 4)) (n : ℕ) :
    Filter.Tendsto (fun s => ∫ z, Λ s z * lineIter (ℓ.map coordDir) (scaledShell h n) (x - z))
        (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ
          (fun z => lineIter (ℓ.map coordDir) (scaledShell h n) (x - z)))) ∧
    |parabolicSemigroup.pairing Λ (fun z => lineIter (ℓ.map coordDir) (scaledShell h n) (x - z))| ≤
      (2 ^ q * C) * (∑ a ∈ A, pairingWeight a) *
        ((∫ w, |lineIter (ℓ.map coordDir) h w|) +
          ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w|) *
        (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n) := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam2 : (2 : ℝ)⁻¹ ^ n ≤ 2 :=
    (pow_le_one₀ (by norm_num) (by norm_num)).trans (by norm_num)
  have hg := contDiff_scaledShell h0 n
  have hF : ContDiff ℝ ∞ (lineIter (ℓ.map coordDir) (scaledShell h n)) := contDiff_lineIter hg _
  have hsupp : ∀ w, (2 : ℝ)⁻¹ ^ n < parabolicNorm w →
      lineIter (ℓ.map coordDir) (scaledShell h n) w = 0 := fun w hw =>
    lineIter_eq_zero_of_isOpen (U := {w | (2 : ℝ)⁻¹ ^ n < parabolicNorm w})
      (isOpen_lt continuous_const continuous_parabolicNorm) _ _
      (fun w hw => scaledShell_eq_zero hs hw) w hw
  have hrp : ((2 : ℝ)⁻¹ ^ n) ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [inv_pow]
  set I : ℝ := ∫ w, |lineIter (ℓ.map coordDir) h w| with hI
  set I' : ℝ := ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w| with hI'
  have key := tendsto_and_abs_pairing_reflect_le_centre_ball (C := 2 ^ q * C) hA hF hlam hlam2
    (by
      have := RegularisingSemigroup.LocalBall.of_growth_le parabolicSemigroup_isMetricScale hΛ hΛm hC hq
        (fun a ha => (hA a ha).2) hloc (lam := (2 : ℝ)⁻¹ ^ n + parabolicNorm (x - x)) (Rm := 1)
        (add_nonneg hlam.le (parabolicNorm_nonneg _))
        (by rw [sub_self, parabolicNorm_zero, add_zero]; exact pow_le_one₀ (by norm_num) (by norm_num))
      exact this.mono_const (le_of_eq (by rw [one_add_one_eq_two]; ring))
        (add_nonneg hlam.le (parabolicNorm_nonneg _))) hsupp
    (c := x)
    (B₀ := ((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * I))
    (B₁ := ((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * I'))
    (integral_abs_word_scaledShell h0 ℓ n).le
    (by
      rw [integral_abs_gen_word_scaledShell h0 ℓ n, hrp]
      refine le_of_eq ?_
      rw [hI']
      field_simp)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  rw [sub_self, parabolicNorm_zero, add_zero]
  have hsum : ∑ a ∈ A, pairingWeight a * (((2 : ℝ)⁻¹ ^ n) ^ a * ((2 : ℝ)⁻¹ ^ n) ^ (γ - a)) =
      (∑ a ∈ A, pairingWeight a) * ((2 : ℝ)⁻¹ ^ n) ^ γ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Real.rpow_add hlam]; congr 2; ring
  rw [hsum, two_rpow_deg_eq]
  ring

end RegularityStructures

end
