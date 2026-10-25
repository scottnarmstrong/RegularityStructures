/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Analysis.Parabolic.Lattice.Count
public import RegularityStructures.Abstract.RegularityStructure
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Constants and counting for the local reconstruction estimates

* `r4ModelConst_nonneg`: the model constant is nonnegative when all degrees below `γ` exceed `-4`;
* `localSumConst`: the constant `∑_{deg i < γ} 12^{γ - deg i} 4^{deg i}` produced by summing the
  increments over the components of `T_{<γ}`;
* `rpow_le_two_pow_abs_mul`: a power of a quantity comparable to `a` is comparable to the power of
  `a`;
* `abs_sum_sum_le_of_active`: counting of the active pairs `(k, l)` in a double sum;
* box cardinalities at the scale `2^{-n}` for balls of radius `2 λ` and `12 · 2^{-n}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_{deg i < γ} 12^{γ - deg i} 4^{deg i}`. -/
def localSumConst (𝒯 : RegularityStructure ι) (γ : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
    (12 : ℝ) ^ (γ - 𝒯.deg i) * (4 : ℝ) ^ 𝒯.deg i

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem r4ModelConst_nonneg (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) : 0 ≤ r4ModelConst 𝒯 γ := by
  unfold r4ModelConst
  have h1 := generatorTimeCoeff_pos
  have h2 := generatorSpaceCoeff_pos
  have hP : 0 ≤ parabolicSemigroup.pairingConst (𝒯.degreesBelow γ) := by
    refine Finset.sum_nonneg fun a ha => ?_
    obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
    have h4 : (0 : ℝ) < 𝒯.deg j + parabolicSemigroup.order := by
      have : parabolicSemigroup.order = 4 := rfl
      rw [this]; linarith [hdeg j hj]
    have : 0 ≤ parabolicSemigroup.order / (𝒯.deg j + parabolicSemigroup.order) :=
      div_nonneg parabolicSemigroup.order_pos.le h4.le
    linarith
  positivity

theorem localSumConst_nonneg (𝒯 : RegularityStructure ι) (γ : ℝ) : 0 ≤ localSumConst 𝒯 γ :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem rpow_le_two_pow_abs_mul {a W : ℝ} (ha : 0 < a) (h1 : a / 2 ≤ W) (h2 : W ≤ 2 * a)
    (e : ℝ) : W ^ e ≤ (2 : ℝ) ^ |e| * a ^ e := by
  have hW : 0 < W := lt_of_lt_of_le (by positivity) h1
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    calc W ^ e ≤ (2 * a) ^ e := Real.rpow_le_rpow hW.le h2 he
      _ = _ := Real.mul_rpow (by norm_num) ha.le
  · rw [abs_of_nonpos he]
    calc W ^ e ≤ (a / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) h1 he
      _ = a ^ e * (2 : ℝ) ^ (-e) := by
        rw [div_eq_mul_inv, Real.mul_rpow ha.le (by norm_num), ← Real.rpow_neg_one,
          ← Real.rpow_mul (by norm_num)]
        congr 2; ring
      _ = _ := mul_comm _ _

theorem abs_sum_sum_le_of_active {κ κ' : Type*} (s' : Finset κ) (s : Finset κ')
    (term : κ → κ' → ℝ) (t : κ → Finset κ') {N B : ℝ} (hB : 0 ≤ B)
    (ht : ∀ k ∈ s', ((t k).card : ℝ) ≤ N)
    (h : ∀ k ∈ s', ∀ l ∈ s, term k l ≠ 0 → l ∈ t k ∧ |term k l| ≤ B) :
    |∑ k ∈ s', ∑ l ∈ s, term k l| ≤ s'.card * (N * B) := by
  classical
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ s', |∑ l ∈ s, term k l| ≤ N * B := fun k hk => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ s, |term k l| ≤ ∑ l ∈ s, if l ∈ t k then B else 0 := by
          refine Finset.sum_le_sum fun l hl => ?_
          by_cases h0 : term k l = 0
          · rw [h0, abs_zero]; split_ifs <;> simp [hB]
          · obtain ⟨h1, h2⟩ := h k hk l hl h0
            simp only [h1, ↓reduceIte]; exact h2
      _ = ((s.filter (· ∈ t k)).card : ℝ) * B := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact (Nat.cast_le.2 (Finset.card_le_card
            fun l hl => (Finset.mem_filter.1 hl).2)).trans (ht k hk)
  calc ∑ k ∈ s', |∑ l ∈ s, term k l| ≤ ∑ _k ∈ s', N * B := Finset.sum_le_sum this
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Cardinality of the box of level-`n+1` lattice points within `2 λ` of `x`, when `2^n λ ≥ 8`. -/
theorem card_latticeBox_succ_le {n : ℕ} {x : ParabolicSpace} {lam : ℝ}
    (hu : 8 ≤ (2 : ℝ) ^ n * lam) :
    ((latticeBox (n + 1) x ((2 * lam) ^ 2) (2 * lam)).card : ℝ) ≤
      24057 * ((2 : ℝ) ^ n * lam) ^ 5 := by
  have hl : 0 < lam := by
    by_contra h
    have : (2 : ℝ) ^ n * lam ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h)
    linarith
  have h := card_latticeBox_le (n := n + 1) (x := x) (rt := (2 * lam) ^ 2) (rs := 2 * lam)
    (by positivity) (by positivity)
  set u := (2 : ℝ) ^ n * lam with hu_def
  have e1 : 2 * (4 : ℝ) ^ (n + 1) * (2 * lam) ^ 2 = 32 * u ^ 2 := by
    have : (4 : ℝ) ^ (n + 1) = 4 * ((2 : ℝ) ^ n) ^ 2 := by
      rw [pow_succ, ← pow_mul, mul_comm n 2, pow_mul]; norm_num; ring
    rw [this, hu_def]; ring
  have e2 : 2 * (2 : ℝ) ^ (n + 1) * (2 * lam) = 8 * u := by
    rw [pow_succ, hu_def]; ring
  rw [e1, e2] at h
  refine h.trans ?_
  have hu2 : (0 : ℝ) ≤ u := by linarith
  have a1 : 32 * u ^ 2 + 2 ≤ 33 * u ^ 2 := by nlinarith
  have a2 : 8 * u + 2 ≤ 9 * u := by nlinarith
  calc (32 * u ^ 2 + 2) * (8 * u + 2) ^ 3 ≤ (33 * u ^ 2) * (9 * u) ^ 3 := by
        gcongr
    _ = 24057 * u ^ 5 := by ring

/-- Cardinality of the box of level-`n` lattice points within `12 · 2^{-n}` of a given point. -/
theorem card_latticeBox_near_le (n : ℕ) (z : ParabolicSpace) :
    ((latticeBox n z ((12 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (12 * ((2 : ℝ) ^ n)⁻¹)).card : ℝ) ≤
      290 * 26 ^ 3 := by
  have hq : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have h := card_latticeBox_le (n := n) (x := z) (rt := (12 * ((2 : ℝ) ^ n)⁻¹) ^ 2)
    (rs := 12 * ((2 : ℝ) ^ n)⁻¹) (by positivity) (by positivity)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have e1 : 2 * (4 : ℝ) ^ n * (12 * ((2 : ℝ) ^ n)⁻¹) ^ 2 = 288 := by
    have : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
    rw [this]; field_simp; norm_num
  have e2 : 2 * (2 : ℝ) ^ n * (12 * ((2 : ℝ) ^ n)⁻¹) = 24 := by
    field_simp; norm_num
  rw [e1, e2] at h
  refine h.trans ?_
  norm_num

end RegularityStructures

end
