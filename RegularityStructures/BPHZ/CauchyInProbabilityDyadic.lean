/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.CauchyInProbability
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic almost-sure Cauchy property and boundedness

Along the dyadic scales `a n = 2⁻ⁿ`, moment bounds
`∫⁻ D (2⁻ⁿ) (2⁻ᵐ)^p ≲ 2^{-θ p min(n,m)}` force, almost surely, that `n ↦ D (2⁻ⁿ) (2⁻ᵐ)` is
Cauchy and that the sizes `S (2⁻ⁿ)` are bounded (Borel–Cantelli applied to the consecutive
differences against the threshold `2^{-θ n / 2}`).

The distance is assumed to satisfy, almost surely, the pseudometric axioms on the dyadic scales,
and the size to satisfy `S (2⁻ⁿ) ≤ S 1 + D (2⁻ⁿ) 1`.  Only the outer measure `P` is used, and
moment bounds are phrased for `AEMeasurable` majorants.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures

section Deterministic

/-- Deterministic core: a pseudometric array with summable consecutive differences is Cauchy
and bounded by the total sum. -/
private theorem cauchy_bdd_of_tsum_ne_top {x : ℕ → ℕ → ℝ≥0∞}
    (hsymm : ∀ n m, x n m = x m n) (hdiag : ∀ n, x n n = 0)
    (htri : ∀ n k m, x n m ≤ x n k + x k m) (hsum : ∑' k, x k (k + 1) ≠ ∞) :
    (∀ δ : ℝ, 0 < δ → ∃ N, ∀ n ≥ N, ∀ m ≥ N, x n m ≤ ENNReal.ofReal δ) ∧
      ∀ n, x n 0 ≤ ∑' k, x k (k + 1) := by
  set T : ℕ → ℝ≥0∞ := fun N => ∑' k, x (k + N) (k + N + 1) with hT
  have step1 : ∀ n j, x n (j + n) ≤ ∑ i ∈ Finset.range j, x (i + n) (i + n + 1) := by
    intro n j
    induction j with
    | zero => simp [hdiag]
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have e : j + 1 + n = j + n + 1 := by omega
      rw [e]
      exact (htri n (j + n) (j + n + 1)).trans (by gcongr)
  have step2 : ∀ n m, n ≤ m → x n m ≤ T n := by
    intro n m hnm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + n := ⟨m - n, by omega⟩
    exact (step1 n j).trans (ENNReal.sum_le_tsum _)
  have step3 : ∀ n m, x n m ≤ T (min n m) := by
    intro n m
    rcases le_total n m with h | h
    · rw [min_eq_left h]; exact step2 n m h
    · rw [min_eq_right h, hsymm]; exact step2 m n h
  have hTlim : Tendsto T atTop (𝓝 0) := ENNReal.tendsto_sum_nat_add _ hsum
  refine ⟨fun δ hδ => ?_, fun n => ?_⟩
  · have hev := (tendsto_order.1 hTlim).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨N, fun n hn m hm => (step3 n m).trans (hN _ (le_min hn hm)).le⟩
  · have := step3 n 0
    simpa [hT] using this

end Deterministic

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A functional with finite `p`-th moment (for an a.e. measurable majorant) is a.e. finite. -/
private theorem ae_ne_top_of_lintegral_rpow_le {f f' : Ω → ℝ≥0∞} {P : Measure Ω}
    {p : ℝ} {c : ℝ≥0∞} (hff' : f ≤ᵐ[P] f') (hf' : AEMeasurable f' P) (hp : 0 < p)
    (hc : ∫⁻ ω, f' ω ^ p ∂P ≤ c) (hcfin : c ≠ ∞) : ∀ᵐ ω ∂P, f ω ≠ ∞ := by
  have h := ae_lt_top' (hf'.pow_const p) (ne_top_of_le_ne_top hcfin hc)
  filter_upwards [hff', h] with ω h1 h2 h3
  rw [h3, top_le_iff] at h1
  rw [h1, ENNReal.top_rpow_of_pos hp] at h2
  exact lt_irrefl _ h2

/-- A sequence of finite terms eventually dominated by a summable sequence is summable. -/
private theorem tsum_ne_top_of_eventually_le {f g : ℕ → ℝ≥0∞} {K : ℕ}
    (hfin : ∀ k, f k ≠ ∞) (hle : ∀ k, K ≤ k → f k ≤ g k) (hg : ∑' k, g k ≠ ∞) :
    ∑' k, f k ≠ ∞ := by
  have hle' : ∀ k, f k ≤ g k + if k < K then f k else 0 := by
    intro k
    by_cases hk : k < K
    · simp [hk]
    · simpa [hk] using hle k (not_lt.1 hk)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle')
  rw [ENNReal.tsum_add]
  refine ENNReal.add_ne_top.2 ⟨hg, ?_⟩
  rw [tsum_eq_sum (s := Finset.range K) (fun b hb => by simp_all)]
  exact ENNReal.sum_ne_top.2 fun k hk => by
    simpa [Finset.mem_range.1 hk] using hfin k

private theorem inv_two_rpow_pow (c : ℝ) (k : ℕ) :
    ((2⁻¹ : ℝ) ^ c) ^ k = (2⁻¹ : ℝ) ^ (c * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

end Helpers

section BorelCantelli

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Borel–Cantelli for the consecutive dyadic differences: almost surely
`D (2⁻ᵏ) (2⁻ᵏ⁻¹) ≤ 2^{-θ k / 2}` for all large `k`. -/
private theorem ae_eventually_consecutive_le {D D' : ℝ → ℝ → Ω → ℝ≥0∞} {θ p C : ℝ}
    (hθ : 0 < θ) (hp : 0 < p) (hC : 0 ≤ C)
    (hDD' : ∀ n m : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ≤ᵐ[P] D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m))
    (hmeas : ∀ n m : ℕ, AEMeasurable (D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m)) P)
    (hmom : ∀ n m : ℕ, ∫⁻ ω, D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ^ p ∂P ≤
      ENNReal.ofReal C * ENNReal.ofReal ((2⁻¹ : ℝ) ^ (θ * p * ((min n m : ℕ) : ℝ)))) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ (k + 1)) ω ≤ ENNReal.ofReal (((2⁻¹ : ℝ) ^ (θ / 2)) ^ k) := by
  have hP : ∀ k : ℕ, P {ω | ENNReal.ofReal (((2⁻¹ : ℝ) ^ (θ / 2)) ^ k) <
      D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ (k + 1)) ω} ≤
      ENNReal.ofReal (C * ((2⁻¹ : ℝ) ^ (θ * p / 2)) ^ k) := by
    intro k
    have hδ : 0 < ((2⁻¹ : ℝ) ^ (θ / 2)) ^ k := by positivity
    refine (measure_lt_le_div_of_lintegral_rpow_le (hDD' k (k + 1)) (hmeas k (k + 1)) hp hδ
      (hmom k (k + 1))).trans (le_of_eq ?_)
    rw [min_eq_left (Nat.le_succ k), ENNReal.ofReal_rpow_of_pos hδ, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    have e1 : (((2⁻¹ : ℝ) ^ (θ / 2)) ^ k) ^ p = (2⁻¹ : ℝ) ^ (θ / 2 * k * p) := by
      rw [inv_two_rpow_pow, ← Real.rpow_mul (by positivity)]
    rw [e1, inv_two_rpow_pow, mul_div_assoc, ← Real.rpow_sub (by positivity)]
    congr 2
    ring
  have hq : (2⁻¹ : ℝ) ^ (θ * p / 2) < 1 :=
    Real.rpow_lt_one (by positivity) (by norm_num) (by positivity)
  have hsum : ∑' k : ℕ, P {ω | ENNReal.ofReal (((2⁻¹ : ℝ) ^ (θ / 2)) ^ k) <
      D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ (k + 1)) ω} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hP)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      ((summable_geometric_of_lt_one (by positivity) hq).mul_left C)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk
  exact not_lt.1 hk

end BorelCantelli

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Dyadic almost-sure Cauchy property and boundedness.**  Let `a n = 2⁻ⁿ`.  Suppose
`D (a n) (a m)` and `S (a n)` have a.e. measurable majorants `D'`, `S'` with
`∫⁻ D'^p ≤ C 2^{-θ p min(n,m)}` and `∫⁻ S'^p ≤ C` (any `θ, p > 0` suffice), and suppose almost
surely that `D` is symmetric, vanishes on the diagonal and satisfies the triangle inequality on
the dyadic scales, and that `S (a n) ≤ S (a 0) + D (a n) (a 0)`.  Then almost surely `D (a n) (a m)`
is Cauchy as `n, m → ∞` and `S (a n)` is bounded. -/
theorem ae_cauchy_and_bounded_of_dyadic_lintegral_rpow_le
    {D D' : ℝ → ℝ → Ω → ℝ≥0∞} {S : ℝ → Ω → ℝ≥0∞} {S' : ℕ → Ω → ℝ≥0∞} {θ p C : ℝ}
    (hθ : 0 < θ) (hp : 0 < p) (hC : 0 ≤ C)
    (hDD' : ∀ n m : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ≤ᵐ[P] D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m))
    (hDmeas : ∀ n m : ℕ, AEMeasurable (D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m)) P)
    (hDmom : ∀ n m : ℕ, ∫⁻ ω, D' ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ^ p ∂P ≤
      ENNReal.ofReal C * ENNReal.ofReal ((2⁻¹ : ℝ) ^ (θ * p * ((min n m : ℕ) : ℝ))))
    (hSS' : ∀ n : ℕ, S ((2⁻¹ : ℝ) ^ n) ≤ᵐ[P] S' n)
    (hSmeas : ∀ n : ℕ, AEMeasurable (S' n) P)
    (hSmom : ∀ n : ℕ, ∫⁻ ω, S' n ω ^ p ∂P ≤ ENNReal.ofReal C)
    (hsymm : ∀ᵐ ω ∂P, ∀ n m : ℕ,
      D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω = D ((2⁻¹ : ℝ) ^ m) ((2⁻¹ : ℝ) ^ n) ω)
    (hdiag : ∀ᵐ ω ∂P, ∀ n : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ n) ω = 0)
    (htri : ∀ᵐ ω ∂P, ∀ n k m : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ≤
      D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ k) ω + D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ m) ω)
    (hS : ∀ᵐ ω ∂P, ∀ n : ℕ, S ((2⁻¹ : ℝ) ^ n) ω ≤
      S ((2⁻¹ : ℝ) ^ 0) ω + D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ 0) ω) :
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ≤ ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ, S ((2⁻¹ : ℝ) ^ n) ω ≤ ENNReal.ofReal B := by
  have hfin : ∀ᵐ ω ∂P, ∀ k : ℕ,
      D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ (k + 1)) ω ≠ ∞ := by
    rw [ae_all_iff]
    intro k
    refine ae_ne_top_of_lintegral_rpow_le (hDD' k (k + 1)) (hDmeas k (k + 1)) hp
      (hDmom k (k + 1)) ?_
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hS0 := ae_ne_top_of_lintegral_rpow_le (hSS' 0) (hSmeas 0) hp (hSmom 0)
    ENNReal.ofReal_ne_top
  have hBC := ae_eventually_consecutive_le hθ hp hC hDD' hDmeas hDmom
  have hr : (2⁻¹ : ℝ) ^ (θ / 2) < 1 := Real.rpow_lt_one (by positivity) (by norm_num) (by positivity)
  have hgsum : ∑' k : ℕ, ENNReal.ofReal (((2⁻¹ : ℝ) ^ (θ / 2)) ^ k) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by positivity) hr)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [hfin, hBC, hsymm, hdiag, htri, hS, hS0] with ω h1 h2 h3 h4 h5 h6 h7
  obtain ⟨K, hK⟩ := eventually_atTop.1 h2
  have hsum := tsum_ne_top_of_eventually_le (f := fun k => D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ (k + 1)) ω)
    h1 hK hgsum
  obtain ⟨hcau, hbdd⟩ := cauchy_bdd_of_tsum_ne_top
    (x := fun n m => D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω) h3 h4 h5 hsum
  refine ⟨fun δ hδ => ?_, ⟨(S ((2⁻¹ : ℝ) ^ 0) ω + ∑' k, D ((2⁻¹ : ℝ) ^ k)
    ((2⁻¹ : ℝ) ^ (k + 1)) ω).toReal, fun n => ?_⟩⟩
  · obtain ⟨N, hN⟩ := hcau δ hδ
    exact ⟨N, hN⟩
  · rw [ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨h7, hsum⟩)]
    exact (h6 n).trans (by gcongr; exact hbdd n)

end RegularityStructures
