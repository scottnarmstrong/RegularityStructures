/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.SmoothNorm
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Dyadic partition of unity

`dyadicCutoff r = smoothTransition (2 - r)` is `1` for `r ≤ 1` and `0` for `r ≥ 2`, and
`dyadicBump r = dyadicCutoff r - dyadicCutoff (2 r)` is supported in `[1/2, 2]`. The bumps telescope:
`∑_{n<N} dyadicBump (2ⁿ r) = dyadicCutoff r - dyadicCutoff (2ᴺ r)`, so on `(0, ∞)` they sum to
`dyadicCutoff r`. Composed with `smoothParabolicNorm` they give the dyadic shells
`K_n(z) = K̄(z) φ(2ⁿ N(z))` of [Hai14, Lemma 5.5] (arXiv:1303.5113v4).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A smooth cutoff, `1` on `(-∞, 1]` and `0` on `[2, ∞)`. -/
def dyadicCutoff (r : ℝ) : ℝ := Real.smoothTransition (2 - r)

/-- The dyadic bump `χ(r) - χ(2r)`, supported in `[1/2, 2]`. -/
def dyadicBump (r : ℝ) : ℝ := dyadicCutoff r - dyadicCutoff (2 * r)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem dyadicCutoff_eq_one {r : ℝ} (hr : r ≤ 1) : dyadicCutoff r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem dyadicCutoff_eq_zero {r : ℝ} (hr : 2 ≤ r) : dyadicCutoff r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

open scoped ContDiff in
theorem contDiff_dyadicCutoff : ContDiff ℝ ∞ dyadicCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem dyadicCutoff_nonneg (r : ℝ) : 0 ≤ dyadicCutoff r :=
  Real.smoothTransition.nonneg _

theorem dyadicCutoff_le_one (r : ℝ) : dyadicCutoff r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem dyadicBump_eq_zero_of_le {r : ℝ} (hr : r ≤ 1 / 2) : dyadicBump r = 0 := by
  unfold dyadicBump
  rw [dyadicCutoff_eq_one (by linarith), dyadicCutoff_eq_one (by linarith)]
  simp

theorem dyadicBump_eq_zero_of_ge {r : ℝ} (hr : 2 ≤ r) : dyadicBump r = 0 := by
  unfold dyadicBump
  rw [dyadicCutoff_eq_zero hr, dyadicCutoff_eq_zero (by linarith)]
  simp

open scoped ContDiff in
theorem contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCutoff.sub (contDiff_dyadicCutoff.comp (contDiff_const.mul contDiff_id))

theorem sum_range_dyadicBump (N : ℕ) (r : ℝ) :
    ∑ n ∈ Finset.range N, dyadicBump (2 ^ n * r) = dyadicCutoff r - dyadicCutoff (2 ^ N * r) := by
  have h : ∀ n : ℕ, dyadicBump (2 ^ n * r) = dyadicCutoff (2 ^ n * r) - dyadicCutoff (2 ^ (n + 1) * r) := by
    intro n
    unfold dyadicBump
    rw [pow_succ, mul_comm ((2 : ℝ) ^ n) 2, mul_assoc]
  simp_rw [h]
  rw [Finset.sum_range_sub' (fun n : ℕ => dyadicCutoff (2 ^ n * r))]
  simp

/-- Partition of unity on `(0, ∞)`: the dyadic bumps sum to `dyadicCutoff`. -/
theorem hasSum_dyadicBump {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : ℕ => dyadicBump (2 ^ n * r)) (dyadicCutoff r) := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (2 / r) (by norm_num : (1 : ℝ) < 2)
  have hM' : 2 ≤ 2 ^ M * r := by
    rw [div_lt_iff₀ hr] at hM
    exact hM.le
  have h0 : ∀ n ∉ Finset.range M, dyadicBump (2 ^ n * r) = 0 := by
    intro n hn
    have hn' : M ≤ n := by simpa using hn
    refine dyadicBump_eq_zero_of_ge ?_
    calc (2 : ℝ) ≤ 2 ^ M * r := hM'
      _ ≤ 2 ^ n * r :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn') hr.le
  have : HasSum (fun n : ℕ => dyadicBump (2 ^ n * r))
      (∑ n ∈ Finset.range M, dyadicBump (2 ^ n * r)) := hasSum_sum_of_ne_finset_zero h0
  rwa [sum_range_dyadicBump, dyadicCutoff_eq_zero hM', sub_zero] at this

theorem tsum_dyadicBump {r : ℝ} (hr : 0 < r) :
    ∑' n : ℕ, dyadicBump (2 ^ n * r) = dyadicCutoff r :=
  (hasSum_dyadicBump hr).tsum_eq

open scoped ContDiff in
/-- A smooth function of one variable vanishing near `0` gives a smooth function on `ℝ⁴` when
composed with `smoothParabolicNorm`. -/
theorem contDiff_comp_smoothParabolicNorm {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ r ≤ ε, g r = 0) : ContDiff ℝ ∞ fun z => g (smoothParabolicNorm z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hopen : IsOpen {w : ParabolicSpace | smoothParabolicNorm w < ε} :=
      isOpen_lt continuous_smoothParabolicNorm continuous_const
    have hmem : (0 : ParabolicSpace) ∈ {w : ParabolicSpace | smoothParabolicNorm w < ε} := by
      simpa [smoothParabolicNorm_eq_zero_iff.2 rfl] using hε
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact h0 _ hw.le
  · exact (hg.contDiffAt).comp z (contDiffAt_smoothParabolicNorm hz)

open scoped ContDiff in
/-- The dyadic shell `z ↦ dyadicBump (2ⁿ N(z))` is smooth on all of `ℝ⁴`. -/
theorem contDiff_dyadicBump_smoothParabolicNorm (n : ℕ) :
    ContDiff ℝ ∞ fun z => dyadicBump (2 ^ n * smoothParabolicNorm z) := by
  have hpos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  refine contDiff_comp_smoothParabolicNorm (g := fun r => dyadicBump (2 ^ n * r))
    (contDiff_dyadicBump.comp (contDiff_const.mul contDiff_id)) (ε := 1 / (2 * 2 ^ n))
    (by positivity) ?_
  intro r hr
  refine dyadicBump_eq_zero_of_le ?_
  rw [le_div_iff₀ (by positivity)] at hr
  linarith

end RegularityStructures

end
