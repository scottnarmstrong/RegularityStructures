/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorSplit
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSeries

/-!
# Summation over the dyadic scales

If `Λ` has local order `γ > -2` at `x` with exponents `a > -2`, and `γ + 2 ∉ ℕ`, then

  `∑_n |⟨Λ, K^α_{n;xy}⟩| ≤ c C ‖y - x‖_𝔰^{γ+2}`  (`exists_tsum_abs_pairing_taylorKernel_le`),

`α = γ`, `c` depending only on `h, A, γ` [Hai14, (5.16)/proof of Lemma 5.19].  The scales
`2^{-n} ≥ ‖y - x‖` use the Taylor estimate (`exists_abs_pairing_taylorKernel_le`), the scales
`2^{-n} < ‖y - x‖` the two separate pieces (`abs_pairing_taylorKernel_small_le`).
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem hasSum_list_sum {ι : Type*} (l : List ι) (f : ι → ℕ → ℝ) (a : ι → ℝ)
    (hf : ∀ i ∈ l, HasSum (f i) (a i)) :
    HasSum (fun n => (l.map fun i => f i n).sum) (l.map a).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf i (List.mem_cons_self ..)).add (ih fun j hj => hf j (List.mem_cons_of_mem _ hj))

theorem tail_piece_le {d u : ℝ} (hd : 0 < d) (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) {m : ℕ}
    (hm : 1 < d * 2 ^ m) :
    u * ((2 : ℝ) ^ (-ε)) ^ m / (1 - (2 : ℝ) ^ (-ε)) ≤ u * d ^ ε / (1 - (2 : ℝ) ^ (-ε)) := by
  have hr : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rpow_two_pow_le hε hd hm) hu)
    (by linarith)

theorem taylor_series_core {γ C d I₀ Pw : ℝ} (hC : 0 ≤ C) (hd : 0 < d) {A : Finset ℝ}
    (hA : ∀ a ∈ A, -2 < a ∧ a ≤ γ) (hI₀ : 0 ≤ I₀)
    (hpw : ∀ a ∈ A, 0 ≤ pairingWeight a) (hPw : 0 ≤ Pw)
    (𝔈 : List (List (Fin 4))) (κ : List (Fin 4) → ℝ) (hκ : ∀ ℓ, 0 ≤ κ ℓ)
    (hdeg : ∀ ℓ ∈ 𝔈, γ + 2 < (indexWeight ℓ : ℝ))
    (J : (Fin 4 →₀ ℕ) → ℝ) (hJ : ∀ k, 0 ≤ J k) (S : ℕ → ℝ) (hS0 : ∀ n, 0 ≤ S n) {m : ℕ}
    (hm2 : ∀ n, m ≤ n → 1 < d * 2 ^ n) (hm3 : m = 0 ∨ d * 2 ^ m ≤ 2)
    (hT : ∀ n < m, S n ≤ C * (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
      (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum)
    (hB : ∀ n, m ≤ n → S n ≤ I₀ * C * (∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
          ((2 : ℝ)⁻¹ ^ n + d) ^ (γ - a))) +
      ∑ k ∈ taylorIdx (γ + 2), d ^ multiDeg k * (C * Pw * J k *
          (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n))) :
    Summable S ∧ ∑' n, S n ≤
      ((𝔈.map fun ℓ => κ ℓ * ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - (γ + 2)) /
        ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - (γ + 2)) - 1))).sum +
      (∑ a ∈ A, I₀ * pairingWeight a * (2 : ℝ) ^ (γ - a) / (1 - (2 : ℝ) ^ (-(a + 2)))) +
      ∑ k ∈ taylorIdx (γ + 2), Pw * J k /
        (1 - (2 : ℝ) ^ (-((γ + 2) - (multiDeg k : ℝ))))) * C * d ^ (γ + 2) := by
  classical
  set σ : ℝ := γ + 2 with hσ
  have hd0 : 0 ≤ d := hd.le
  -- the majorant pieces
  set Hd : ℕ → ℝ := fun n => (𝔈.map fun ℓ => headSeq (C * κ ℓ * d ^ indexWeight ℓ)
    ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - σ)) m n).sum with hHd
  set Ta : ℕ → ℝ := fun n => ∑ a ∈ A, tailSeq (C * I₀ * pairingWeight a * (2 * d) ^ (γ - a))
    ((2 : ℝ) ^ (-(a + 2))) m n with hTa
  set Tk : ℕ → ℝ := fun n => ∑ k ∈ taylorIdx σ, tailSeq (d ^ multiDeg k * (C * Pw * J k))
    ((2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) m n with hTk
  have hHS : HasSum Hd (𝔈.map fun ℓ => ∑ n ∈ Finset.range m,
      C * κ ℓ * d ^ indexWeight ℓ * ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - σ)) ^ n).sum :=
    hasSum_list_sum 𝔈 _ _ fun ℓ _ => hasSum_headSeq _ _ m
  have hAr : ∀ a ∈ A, (2 : ℝ) ^ (-(a + 2)) < 1 := fun a ha =>
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [(hA a ha).1])
  have hKr : ∀ k ∈ taylorIdx σ, (2 : ℝ) ^ (-(σ - (multiDeg k : ℝ))) < 1 := fun k hk =>
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [(mem_taylorIdx_iff k).1 hk])
  have hTaS : HasSum Ta (∑ a ∈ A, C * I₀ * pairingWeight a * (2 * d) ^ (γ - a) *
      ((2 : ℝ) ^ (-(a + 2))) ^ m / (1 - (2 : ℝ) ^ (-(a + 2)))) :=
    hasSum_sum fun a ha => hasSum_tailSeq (Real.rpow_nonneg (by norm_num) _) (hAr a ha) _ m
  have hTkS : HasSum Tk (∑ k ∈ taylorIdx σ, d ^ multiDeg k * (C * Pw * J k) *
      ((2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) ^ m / (1 - (2 : ℝ) ^ (-(σ - (multiDeg k : ℝ))))) :=
    hasSum_sum fun k hk => hasSum_tailSeq (Real.rpow_nonneg (by norm_num) _) (hKr k hk) _ m
  have hTot := (hHS.add hTaS).add hTkS
  -- domination
  have hdom : ∀ n, S n ≤ Hd n + Ta n + Tk n := by
    intro n
    by_cases hn : n < m
    · have hTn : Ta n = 0 := Finset.sum_eq_zero fun a _ => by simp [tailSeq, not_le.2 hn]
      have hKn : Tk n = 0 := Finset.sum_eq_zero fun k _ => by simp [tailSeq, not_le.2 hn]
      have hHn : Hd n = C * (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
          (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum := by
        simp only [hHd, headSeq, hn, ite_true]
        rw [← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun ℓ _ => ?_
        rw [← Real.rpow_mul_natCast (by norm_num)]
        have : ((indexWeight ℓ : ℝ) - σ) * n = ((indexWeight ℓ : ℝ) - γ - 2) * n := by
          rw [hσ]; ring
        rw [this]; ring
      rw [hTn, hKn, add_zero, add_zero, hHn]
      exact hT n hn
    · have hmn : m ≤ n := not_lt.1 hn
      have hHn : Hd n = 0 := by
        simp only [hHd, headSeq, hn, ite_false]
        simp
      have hq : (2 : ℝ)⁻¹ ^ n ≤ d := by
        have h2 : (0 : ℝ) < 2 ^ n := by positivity
        have := hm2 n hmn
        rw [inv_pow, inv_le_comm₀ h2 hd, inv_eq_one_div, div_le_iff₀ hd]
        linarith
      have hTan : Ta n = ∑ a ∈ A, C * I₀ * pairingWeight a * (2 * d) ^ (γ - a) *
          ((2 : ℝ) ^ (-(a + 2))) ^ n := by
        simp only [hTa, tailSeq, hmn, ite_true]
      have hKn : Tk n = ∑ k ∈ taylorIdx σ, d ^ multiDeg k * (C * Pw * J k) *
          ((2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) ^ n := by
        simp only [hTk, tailSeq, hmn, ite_true]
      rw [hHn, zero_add, hTan, hKn]
      refine (hB n hmn).trans (add_le_add ?_ ?_)
      · rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a ha => ?_
        have hγa : 0 ≤ γ - a := sub_nonneg.2 (hA a ha).2
        have h1 : ((2 : ℝ)⁻¹ ^ n + d) ^ (γ - a) ≤ (2 * d) ^ (γ - a) :=
          Real.rpow_le_rpow (by positivity) (by linarith) hγa
        have h2 : ((2 : ℝ) ^ (-(a + 2))) ^ n = (2 : ℝ) ^ (-(a + 2) * n) := by
          rw [Real.rpow_mul_natCast (by norm_num)]
        rw [h2]
        have h3 : 0 ≤ (2 : ℝ) ^ (-(a + 2) * n) := Real.rpow_nonneg (by norm_num) _
        have h4 : 0 ≤ I₀ * C * pairingWeight a := mul_nonneg (mul_nonneg hI₀ hC) (hpw a ha)
        calc I₀ * C * (pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) * ((2 : ℝ)⁻¹ ^ n + d) ^ (γ - a)))
            = (I₀ * C * pairingWeight a) * (2 : ℝ) ^ (-(a + 2) * n) *
                ((2 : ℝ)⁻¹ ^ n + d) ^ (γ - a) := by ring
          _ ≤ (I₀ * C * pairingWeight a) * (2 : ℝ) ^ (-(a + 2) * n) * (2 * d) ^ (γ - a) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg h4 h3)
          _ = _ := by ring
      · refine Finset.sum_le_sum fun k _ => ?_
        refine le_of_eq ?_
        have h2 : ((2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) ^ n =
            (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n) := by
          rw [← Real.rpow_mul_natCast (by norm_num)]
          congr 1; rw [hσ]; ring
        rw [h2]; ring
  have hsum : Summable S := Summable.of_nonneg_of_le hS0 hdom hTot.summable
  refine ⟨hsum, ?_⟩
  refine (hsum.tsum_le_tsum hdom hTot.summable).trans (le_of_eq_of_le hTot.tsum_eq ?_)
  have hm : 1 < d * 2 ^ m := hm2 m le_rfl
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd0 _
  -- the three parts
  have hH : (𝔈.map fun ℓ => ∑ n ∈ Finset.range m,
        C * κ ℓ * d ^ indexWeight ℓ * ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - σ)) ^ n).sum ≤
      (𝔈.map fun ℓ => κ ℓ * ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - σ) /
        ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - σ) - 1))).sum * C * d ^ σ := by
    rw [mul_assoc, ← List.sum_map_mul_right]
    refine List.sum_le_sum fun ℓ hℓ => ?_
    have hδ : 0 < (indexWeight ℓ : ℝ) - σ := by linarith [hdeg ℓ hℓ]
    have := head_piece_le hd (mul_nonneg hC (hκ ℓ)) hδ (indexWeight ℓ) (σ := σ) (by ring) hm3
    refine this.trans (le_of_eq ?_)
    ring
  have hAp : (∑ a ∈ A, C * I₀ * pairingWeight a * (2 * d) ^ (γ - a) *
        ((2 : ℝ) ^ (-(a + 2))) ^ m / (1 - (2 : ℝ) ^ (-(a + 2)))) ≤
      (∑ a ∈ A, I₀ * pairingWeight a * (2 : ℝ) ^ (γ - a) / (1 - (2 : ℝ) ^ (-(a + 2)))) *
        C * d ^ σ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun a ha => ?_
    have hε : 0 < a + 2 := by linarith [(hA a ha).1]
    have hu : 0 ≤ C * I₀ * pairingWeight a * (2 * d) ^ (γ - a) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC hI₀) (hpw a ha)) (Real.rpow_nonneg (by positivity) _)
    refine (tail_piece_le hd hu hε hm).trans (le_of_eq ?_)
    have e : d ^ (a + 2) * d ^ (γ - a) = d ^ σ := by
      rw [← Real.rpow_add hd, hσ]; congr 1; ring
    rw [Real.mul_rpow (by norm_num) hd0]
    have hne : (1 - (2 : ℝ) ^ (-(a + 2))) ≠ 0 := by
      have := hAr a ha; intro h; linarith
    field_simp
    rw [← e]; ring
  have hKp : (∑ k ∈ taylorIdx σ, d ^ multiDeg k * (C * Pw * J k) *
        ((2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) ^ m /
          (1 - (2 : ℝ) ^ (-(σ - (multiDeg k : ℝ))))) ≤
      (∑ k ∈ taylorIdx σ, Pw * J k / (1 - (2 : ℝ) ^ (-(σ - (multiDeg k : ℝ))))) * C * d ^ σ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := (mem_taylorIdx_iff k).1 hk
    have hε : 0 < σ - (multiDeg k : ℝ) := by linarith
    have hu : 0 ≤ d ^ multiDeg k * (C * Pw * J k) :=
      mul_nonneg (pow_nonneg hd0 _) (mul_nonneg (mul_nonneg hC hPw) (hJ k))
    refine (tail_piece_le hd hu hε hm).trans (le_of_eq ?_)
    have e : d ^ multiDeg k * d ^ (σ - (multiDeg k : ℝ)) = d ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hd]; congr 1; ring
    have hne : (1 - (2 : ℝ) ^ (-(σ - (multiDeg k : ℝ)))) ≠ 0 := by
      have := hKr k hk; intro h; linarith
    field_simp
    rw [← e]; ring
  calc _ ≤ _ := add_le_add (add_le_add hH hAp) hKp
    _ = _ := by ring

theorem exists_tsum_abs_pairing_taylorKernel_le {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -2 < a ∧ a ≤ γ) (hγ : -2 < γ)
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ} {x y : ParabolicSpace},
      Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
      parabolicSemigroup.IsLocalOrder Λ x γ A C →
      Summable (fun n : ℕ => |parabolicSemigroup.pairing Λ (taylorKernel h n (γ + 2) x y)|) ∧
      ∑' n : ℕ, |parabolicSemigroup.pairing Λ (taylorKernel h n (γ + 2) x y)| ≤
        c * C * parabolicNorm (y - x) ^ (γ + 2) := by
  classical
  have hA4 : ∀ a ∈ A, -4 < a ∧ a ≤ γ := fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩
  obtain ⟨𝔈, κ, hκ, hdeg, hbound⟩ := exists_abs_pairing_taylorKernel_le h0 hs hA4
  set I₀ : ℝ := (∫ w, |h w|) + ∫ w, |parabolicGenerator h w| with hI₀
  set Pw : ℝ := ∑ a ∈ A, pairingWeight a with hPw
  set J : (Fin 4 →₀ ℕ) → ℝ := fun k => (∫ w, |lineIter (multiDirs k) h w|) +
    ∫ w, |lineIter (multiDirs k) (parabolicGenerator h) w| with hJ
  have hI₀0 : 0 ≤ I₀ := add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)
  have hPw0 : 0 ≤ Pw := Finset.sum_nonneg fun a ha => pairingWeight_nonneg (hA4 a ha).1
  have hJ0 : ∀ k, 0 ≤ J k := fun k => add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)
  have hpw : ∀ a ∈ A, 0 ≤ pairingWeight a := fun a ha => pairingWeight_nonneg (hA4 a ha).1
  -- the constants
  set cH : ℝ := (𝔈.map fun ℓ => κ ℓ * ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - (γ + 2)) /
    ((2 : ℝ) ^ ((indexWeight ℓ : ℝ) - (γ + 2)) - 1))).sum with hcH
  set cA : ℝ := ∑ a ∈ A, I₀ * pairingWeight a * (2 : ℝ) ^ (γ - a) / (1 - (2 : ℝ) ^ (-(a + 2)))
    with hcA
  set cK : ℝ := ∑ k ∈ taylorIdx (γ + 2), Pw * J k /
    (1 - (2 : ℝ) ^ (-((γ + 2) - (multiDeg k : ℝ)))) with hcK
  have hcH0 : 0 ≤ cH := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((indexWeight ℓ : ℝ) - (γ + 2)) :=
      Real.one_le_rpow (by norm_num) (by linarith [(hdeg ℓ hℓ).1])
    exact mul_nonneg (hκ ℓ) (div_nonneg (by linarith) (by linarith))
  have hcA0 : 0 ≤ cA := by
    refine Finset.sum_nonneg fun a ha => ?_
    have h1 : (2 : ℝ) ^ (-(a + 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [(hA a ha).1])
    exact div_nonneg (mul_nonneg (mul_nonneg hI₀0 (hpw a ha)) (Real.rpow_nonneg (by norm_num) _))
      (by linarith)
  have hcK0 : 0 ≤ cK := by
    refine Finset.sum_nonneg fun k hk => ?_
    have hk' := (mem_taylorIdx_iff k).1 hk
    have h1 : (2 : ℝ) ^ (-((γ + 2) - (multiDeg k : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact div_nonneg (mul_nonneg hPw0 (hJ0 k)) (by linarith)
  refine ⟨cH + cA + cK, add_nonneg (add_nonneg hcH0 hcA0) hcK0, ?_⟩
  intro Λ C x y hΛ hΛm hC hloc
  set d : ℝ := parabolicNorm (y - x) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  set S : ℕ → ℝ := fun n => |parabolicSemigroup.pairing Λ (taylorKernel h n (γ + 2) x y)| with hSdef
  have hS0 : ∀ n, 0 ≤ S n := fun n => abs_nonneg _
  have hT : ∀ n, d ≤ (2 : ℝ)⁻¹ ^ n → S n ≤ C * (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
      (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum := fun n hn =>
    hbound hΛ hΛm hC hloc n hn
  rcases hd0.eq_or_lt with hd00 | hdpos
  · -- `x = y` (in the parabolic sense): every term vanishes
    have hz : ∀ n, S n = 0 := by
      intro n
      have := hT n (by rw [← hd00]; positivity)
      refine le_antisymm (this.trans (le_of_eq ?_)) (hS0 n)
      rw [← hd00]
      have : (𝔈.map fun ℓ => κ ℓ * ((0 : ℝ) ^ indexWeight ℓ *
          (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum = 0 := by
        refine List.sum_eq_zero fun v hv => ?_
        obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hv
        have hw : indexWeight ℓ ≠ 0 := by
          intro h0'
          have := (hdeg ℓ hℓ).1
          rw [h0'] at this
          norm_num at this
          linarith
        simp [hw]
      rw [this, mul_zero]
    have hS : S = fun _ => 0 := funext hz
    refine ⟨?_, ?_⟩
    · rw [hS]; exact summable_zero
    · rw [hS, tsum_zero, ← hd00]
      rw [Real.zero_rpow (by linarith)]
      simp
  · obtain ⟨m, hm1, hm2, hm3⟩ := exists_splitIndex' hdpos
    refine taylor_series_core hC hdpos hA hI₀0 hpw hPw0 𝔈 κ hκ
      (fun ℓ hℓ => (hdeg ℓ hℓ).2 hnat) J hJ0 S hS0 hm2 hm3 ?_ ?_
    · intro n hn
      refine hT n ?_
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have h3 := hm1 n hn
      rw [inv_pow]
      calc d = (d * 2 ^ n) * ((2 : ℝ) ^ n)⁻¹ := by field_simp
        _ ≤ 1 * ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 h2.le)
        _ = _ := one_mul _
    · intro n _
      exact abs_pairing_taylorKernel_small_le hΛ hΛm h0 hs hA4 hC hloc (γ + 2) n

end RegularityStructures

end
