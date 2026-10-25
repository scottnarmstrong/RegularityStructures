/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductDefs
public import RegularityStructures.Abstract.Model

/-!
# Coordinate bounds for products and for the structure group

Estimates used in the proof of [Hai14, Theorem 4.7]:

* `Model.abs_gammaMap_single_apply_le`: `|(Γ_{yx} e_{i'})_i| ≤ (1 + C_Γ) d(y, x)^{deg i' − deg i}`
  for `deg i ≤ deg i' < γ` under the model bound `GammaBoundOn γ C_Γ`; the coordinates with
  `deg i > deg i'` vanish (`gammaMap_single_apply_eq_zero`);
* `Model.abs_gammaMap_homogeneousProj_apply_le`: the same for `Γ_{yx} Q_m a`;
* `Model.abs_mul_gammaMap_homogeneousProj_apply_le`: the bound
  `|(Γ_{yx} Q_m a ⋆ Γ_{yx} Q_n b)_k| ≲ d(y, x)^{m + n − deg k}` of [Hai14, (4.6)];
* `GradedProduct.abs_mul_apply_le_of_left_increment`, `…_of_right_increment`,
  `…_of_increments`: the bounds on the three terms `(Γf₁ − f₁) ⋆ f₂`, `f₁ ⋆ (Γf₂ − f₂)` and
  `(Γf₁ − f₁) ⋆ (Γf₂ − f₂)` of [Hai14, (4.4)] at distances `d ≤ 1`.

Source: [Hai14] = arXiv:1303.5113v4, proof of Theorem 4.7.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- `|(∑_{m, n ∈ s} u_{mn})_k| ≤ |s|² X` if every `|(u_{mn})_k| ≤ X`. -/
theorem abs_sum_sum_apply_le {s : Finset ℝ} (u : ℝ → ℝ → ι → ℝ) (k : ι) {X : ℝ}
    (h : ∀ m ∈ s, ∀ n ∈ s, |u m n k| ≤ X) :
    |(∑ m ∈ s, ∑ n ∈ s, u m n) k| ≤ s.card * (s.card * X) := by
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ m ∈ s, |(∑ n ∈ s, u m n) k| ≤ s.card * X := by
    intro m hm
    rw [Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul s (fun n => |u m n k|) X (fun n hn => h m hm n hn)
    simpa [nsmul_eq_mul] using this
  have := Finset.sum_le_card_nsmul s (fun m => |(∑ n ∈ s, u m n) k|) _ h1
  simpa [nsmul_eq_mul] using this

omit [DecidableEq ι] in
theorem card_image_deg_le (deg : ι → ℝ) :
    ((Finset.univ.image deg).card : ℝ) ≤ Fintype.card ι := by
  exact_mod_cast Finset.card_image_le.trans_eq Finset.card_univ

omit [DecidableEq ι] in
/-- The double-sum bound with `|s| ≤ |ι|` for `s = deg(ι)`. -/
theorem abs_sum_sum_image_apply_le (deg : ι → ℝ) (u : ℝ → ℝ → ι → ℝ) (k : ι) {X : ℝ}
    (hX : 0 ≤ X) (h : ∀ m ∈ Finset.univ.image deg, ∀ n ∈ Finset.univ.image deg, |u m n k| ≤ X) :
    |(∑ m ∈ Finset.univ.image deg, ∑ n ∈ Finset.univ.image deg, u m n) k| ≤
      Fintype.card ι * (Fintype.card ι * X) := by
  refine (abs_sum_sum_apply_le u k h).trans ?_
  have hc := card_image_deg_le deg
  have hc0 : (0 : ℝ) ≤ ((Finset.univ.image deg).card : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul hc (mul_le_mul_of_nonneg_right hc hX) (mul_nonneg hc0 hX)
    (Nat.cast_nonneg _)

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `(Γ_{yx} e_{i'})_i = 0` if `deg i' < deg i`. -/
theorem gammaMap_single_apply_eq_zero (x y : E) {i' i : ι} (h : 𝒯.deg i' < 𝒯.deg i) :
    M.gammaMap y x (Pi.single i' 1) i = 0 := by
  have h1 := (M.isGradedUnipotent_gammaMap y x) i' i h.le
  have hne : i ≠ i' := by
    rintro rfl
    exact lt_irrefl _ h
  simpa [Pi.single_apply, hne] using h1

/-- `(Γ_{yx} Q_m a)_i = 0` if `m < deg i`. -/
theorem gammaMap_homogeneousProj_apply_eq_zero (x y : E) {m : ℝ} (a : ι → ℝ) {i : ι}
    (h : m < 𝒯.deg i) : M.gammaMap y x (homogeneousProj 𝒯.deg m a) i = 0 := by
  rw [apply_homogeneousProj_apply]
  refine Finset.sum_eq_zero fun i' _ => ?_
  split_ifs with hi'
  · rw [M.gammaMap_single_apply_eq_zero x y (by rw [hi']; exact h), mul_zero]
  · rw [zero_mul]

end Model

end RegularityStructures

end
