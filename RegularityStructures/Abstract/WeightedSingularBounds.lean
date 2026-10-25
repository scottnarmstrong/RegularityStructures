/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductTheorem
public import RegularityStructures.Abstract.WeightedSingularDefs

/-!
# Coordinate bounds for products of singular modelled distributions

Estimates used in the proof of [Hai14, Proposition 6.12]. Throughout, `d = d(y, x)` and
`w = ‖x, y‖_P` with `0 ≤ d ≤ w ≤ 1`, `0 < w`; the target size of a component of degree `ℓ` of an
increment is `d^{γ − ℓ} w^{η − γ}`.

* `rpow_mul_rpow_le_rpow_mul_rpow`: `d^a w^b ≤ d^e w^c` for `0 ≤ e ≤ a`, `c ≤ b + (a − e)`;
  this converts surplus powers of `d` into powers of `w`;
* `GradedProduct.abs_mul_apply_le_weighted_sup`: the sup bound
  `|(a ⋆ b)_k| ≲ w^{(η − deg k) ∧ 0}`;
* `GradedProduct.abs_mul_apply_le_of_right_increment_weighted`,
  `…_of_left_increment_weighted`, `…_of_increments_weighted`: the three terms of
  [Hai14, (4.4)] in the weighted setting;
* `Model.abs_mul_gammaMap_homogeneousProj_apply_le_weighted`: the bound (6.12) on the terms
  `Γ Q_m f₁ ⋆ Γ Q_n f₂` with `m + n ≥ γ`. Here the hypothesis `η ≤ γ` is used: when both
  `m < η₁` and `n < η₂` the exponent of `w` is `m + n − γ ≥ 0`, which is `≥ η − γ` only if
  `η ≤ γ`.

Source: [Hai14] = arXiv:1303.5113v4, proof of Proposition 6.12.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Surplus powers of `d ≤ w` become powers of `w`: `d^a w^b ≤ d^e w^c` for
`0 ≤ e ≤ a` and `c ≤ b + (a − e)`, when `0 ≤ d ≤ w ≤ 1`, `0 < w`. -/
theorem rpow_mul_rpow_le_rpow_mul_rpow {d w a b e c : ℝ} (hd0 : 0 ≤ d) (hdw : d ≤ w)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (he : 0 ≤ e) (hea : e ≤ a) (hc : c ≤ b + (a - e)) :
    d ^ a * w ^ b ≤ d ^ e * w ^ c := by
  have h1 : d ^ a = d ^ e * d ^ (a - e) := by
    rw [← Real.rpow_add_of_nonneg hd0 he (by linarith)]
    congr 1
    ring
  have h2 : d ^ (a - e) ≤ w ^ (a - e) := Real.rpow_le_rpow hd0 hdw (by linarith)
  have h3 : w ^ (a - e) * w ^ b = w ^ (b + (a - e)) := by
    rw [← Real.rpow_add hw0]
    congr 1
    ring
  have h4 : w ^ (b + (a - e)) ≤ w ^ c := Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hc
  calc d ^ a * w ^ b = d ^ e * (d ^ (a - e) * w ^ b) := by rw [h1]; ring
    _ ≤ d ^ e * (w ^ (a - e) * w ^ b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hw0.le _))
          (Real.rpow_nonneg hd0 _)
    _ = d ^ e * w ^ (b + (a - e)) := by rw [h3]
    _ ≤ d ^ e * w ^ c := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hd0 _)

/-- `η ≤ (η_a ∧ i) + η_b` from `η ≤ η_a + η_b` and `η ≤ α + η_b`, `α ≤ i`. -/
theorem le_min_sub_add_of_le {η ηa ηb α i : ℝ} (h₁ : η ≤ ηa + ηb) (h₂ : η ≤ α + ηb)
    (hi : α ≤ i) : η ≤ min (ηa - i) 0 + i + ηb := by
  rcases min_cases (ηa - i) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct)

/-- The sup part of [Hai14, Proposition 6.12]: if `|a_i| ≤ A w^{(η₁ − deg i) ∧ 0}` (with
`a_i = 0` below `α₁`) and `|b_j| ≤ B w^{(η₂ − deg j) ∧ 0}` (with `b_j = 0` below `α₂`), then
`|(a ⋆ b)_k| ≤ ‖⋆‖ A B w^{(η − deg k) ∧ 0}` for `η ≤ (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)`. -/
theorem abs_mul_apply_le_weighted_sup {a b : ι → ℝ} {k : ι} {A B w α₁ α₂ η₁ η₂ η : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ A * w ^ min (η₁ - 𝒯.deg i) 0) (haα : ∀ i, 𝒯.deg i < α₁ → a i = 0)
    (hb : ∀ j, |b j| ≤ B * w ^ min (η₂ - 𝒯.deg j) 0) (hbα : ∀ j, 𝒯.deg j < α₂ → b j = 0)
    (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂) :
    |P.mul a b k| ≤ P.const * (A * B * w ^ min (η - 𝒯.deg k) 0) := by
  have hX : 0 ≤ A * B * w ^ min (η - 𝒯.deg k) 0 :=
    mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg hw0.le _)
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hi : 𝒯.deg i < α₁
  · rw [haα i hi, abs_zero, zero_mul]
    exact hX
  by_cases hj : 𝒯.deg j < α₂
  · rw [hbα j hj, abs_zero, mul_zero]
    exact hX
  have hexp : min (η - 𝒯.deg k) 0 ≤ min (η₁ - 𝒯.deg i) 0 + min (η₂ - 𝒯.deg j) 0 := by
    have h1 := min_le_left (η - 𝒯.deg k) 0
    have h2 := min_le_right (η - 𝒯.deg k) 0
    rcases min_cases (η₁ - 𝒯.deg i) 0 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases min_cases (η₂ - 𝒯.deg j) 0 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;>
      linarith [not_lt.1 hi, not_lt.1 hj]
  calc |a i| * |b j| ≤ (A * w ^ min (η₁ - 𝒯.deg i) 0) * (B * w ^ min (η₂ - 𝒯.deg j) 0) :=
        mul_le_mul (ha i) (hb j) (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg hw0.le _))
    _ = A * B * w ^ (min (η₁ - 𝒯.deg i) 0 + min (η₂ - 𝒯.deg j) 0) := by
        rw [Real.rpow_add hw0]
        ring
    _ ≤ A * B * w ^ min (η - 𝒯.deg k) 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hexp)
          (mul_nonneg hA hB)

/-- The term `f₁ ⋆ (f₂(y) − Γ f₂(x))` of [Hai14, (4.4)] in the weighted setting. -/
theorem abs_mul_apply_le_of_right_increment_weighted {a b : ι → ℝ} {k : ι}
    {A B d w α γb ηa ηb γ η : ℝ} (hd0 : 0 ≤ d) (hdw : d ≤ w) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hk : 𝒯.deg k < γ) (hγ : γ ≤ γb + α) (hη₁ : η ≤ ηa + ηb) (hη₂ : η ≤ α + ηb) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ A * w ^ min (ηa - 𝒯.deg i) 0)
    (haα : ∀ i, 𝒯.deg i < α → a i = 0)
    (hb : ∀ j, 𝒯.deg j < γb → |b j| ≤ B * d ^ (γb - 𝒯.deg j) * w ^ (ηb - γb))
    (hbT : ∀ j, γb ≤ 𝒯.deg j → b j = 0) :
    |P.mul a b k| ≤ P.const * (A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ))) := by
  have hX : 0 ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
    mul_nonneg (mul_nonneg hA hB) (mul_nonneg (Real.rpow_nonneg hd0 _)
      (Real.rpow_nonneg hw0.le _))
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hi : 𝒯.deg i < α
  · rw [haα i hi, abs_zero, zero_mul]
    exact hX
  by_cases hj : 𝒯.deg j < γb
  · have hkey : d ^ (γb - 𝒯.deg j) * w ^ (min (ηa - 𝒯.deg i) 0 + (ηb - γb)) ≤
        d ^ (γ - 𝒯.deg k) * w ^ (η - γ) := by
      refine rpow_mul_rpow_le_rpow_mul_rpow hd0 hdw hw0 hw1 (by linarith) (by linarith) ?_
      have := le_min_sub_add_of_le hη₁ hη₂ (not_lt.1 hi)
      linarith
    calc |a i| * |b j| ≤ (A * w ^ min (ηa - 𝒯.deg i) 0) *
          (B * d ^ (γb - 𝒯.deg j) * w ^ (ηb - γb)) :=
          mul_le_mul (ha i) (hb j hj) (abs_nonneg _)
            (mul_nonneg hA (Real.rpow_nonneg hw0.le _))
      _ = A * B * (d ^ (γb - 𝒯.deg j) * w ^ (min (ηa - 𝒯.deg i) 0 + (ηb - γb))) := by
          rw [Real.rpow_add hw0]
          ring
      _ ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hA hB)
  · rw [hbT j (not_lt.1 hj), abs_zero, mul_zero]
    exact hX

/-- The term `(f₁(y) − Γ f₁(x)) ⋆ f₂` of [Hai14, (4.4)] in the weighted setting. -/
theorem abs_mul_apply_le_of_left_increment_weighted {a b : ι → ℝ} {k : ι}
    {A B d w α γa ηa ηb γ η : ℝ} (hd0 : 0 ≤ d) (hdw : d ≤ w) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hk : 𝒯.deg k < γ) (hγ : γ ≤ γa + α) (hη₁ : η ≤ ηa + ηb) (hη₂ : η ≤ ηa + α) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (ha : ∀ i, 𝒯.deg i < γa → |a i| ≤ A * d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa))
    (haT : ∀ i, γa ≤ 𝒯.deg i → a i = 0) (hb : ∀ j, |b j| ≤ B * w ^ min (ηb - 𝒯.deg j) 0)
    (hbα : ∀ j, 𝒯.deg j < α → b j = 0) :
    |P.mul a b k| ≤ P.const * (A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ))) := by
  have hX : 0 ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
    mul_nonneg (mul_nonneg hA hB) (mul_nonneg (Real.rpow_nonneg hd0 _)
      (Real.rpow_nonneg hw0.le _))
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hj : 𝒯.deg j < α
  · rw [hbα j hj, abs_zero, mul_zero]
    exact hX
  by_cases hi : 𝒯.deg i < γa
  · have hkey : d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa + min (ηb - 𝒯.deg j) 0) ≤
        d ^ (γ - 𝒯.deg k) * w ^ (η - γ) := by
      refine rpow_mul_rpow_le_rpow_mul_rpow hd0 hdw hw0 hw1 (by linarith) (by linarith) ?_
      have := le_min_sub_add_of_le (η := η) (ηa := ηb) (ηb := ηa) (α := α) (i := 𝒯.deg j)
        (by linarith) (by linarith) (not_lt.1 hj)
      linarith
    calc |a i| * |b j| ≤ (A * d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa)) *
          (B * w ^ min (ηb - 𝒯.deg j) 0) :=
          mul_le_mul (ha i hi) (hb j) (abs_nonneg _)
            (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hd0 _)) (Real.rpow_nonneg hw0.le _))
      _ = A * B * (d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa + min (ηb - 𝒯.deg j) 0)) := by
          rw [Real.rpow_add hw0]
          ring
      _ ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hA hB)
  · rw [haT i (not_lt.1 hi), abs_zero, zero_mul]
    exact hX

/-- The term `(f₁(y) − Γ f₁(x)) ⋆ (f₂(y) − Γ f₂(x))` of [Hai14, (4.4)] in the weighted
setting. -/
theorem abs_mul_apply_le_of_increments_weighted {a b : ι → ℝ} {k : ι}
    {A B d w α γa γb ηa ηb γ η : ℝ} (hd0 : 0 ≤ d) (hdw : d ≤ w) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hk : 𝒯.deg k < γ) (hγ : γ ≤ γb + α) (hη : η ≤ ηa + ηb) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, 𝒯.deg i < γa → |a i| ≤ A * d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa))
    (haT : ∀ i, γa ≤ 𝒯.deg i → a i = 0) (haα : ∀ i, 𝒯.deg i < α → a i = 0)
    (hb : ∀ j, 𝒯.deg j < γb → |b j| ≤ B * d ^ (γb - 𝒯.deg j) * w ^ (ηb - γb))
    (hbT : ∀ j, γb ≤ 𝒯.deg j → b j = 0) :
    |P.mul a b k| ≤ P.const * (A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ))) := by
  have hX : 0 ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
    mul_nonneg (mul_nonneg hA hB) (mul_nonneg (Real.rpow_nonneg hd0 _)
      (Real.rpow_nonneg hw0.le _))
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hiα : 𝒯.deg i < α
  · rw [haα i hiα, abs_zero, zero_mul]
    exact hX
  by_cases hi : 𝒯.deg i < γa
  · by_cases hj : 𝒯.deg j < γb
    · have hdd : d ^ (γa - 𝒯.deg i) * d ^ (γb - 𝒯.deg j) =
          d ^ (γa + γb - 𝒯.deg k) := by
        rw [← Real.rpow_add_of_nonneg hd0 (by linarith) (by linarith)]
        congr 1
        linarith
      have hkey : d ^ (γa + γb - 𝒯.deg k) * w ^ (ηa - γa + (ηb - γb)) ≤
          d ^ (γ - 𝒯.deg k) * w ^ (η - γ) :=
        rpow_mul_rpow_le_rpow_mul_rpow hd0 hdw hw0 hw1 (by linarith)
          (by linarith [not_lt.1 hiα]) (by linarith)
      calc |a i| * |b j| ≤ (A * d ^ (γa - 𝒯.deg i) * w ^ (ηa - γa)) *
            (B * d ^ (γb - 𝒯.deg j) * w ^ (ηb - γb)) :=
            mul_le_mul (ha i hi) (hb j hj) (abs_nonneg _)
              (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hd0 _))
                (Real.rpow_nonneg hw0.le _))
        _ = A * B * ((d ^ (γa - 𝒯.deg i) * d ^ (γb - 𝒯.deg j)) *
            w ^ (ηa - γa + (ηb - γb))) := by
            rw [Real.rpow_add hw0]
            ring
        _ = A * B * (d ^ (γa + γb - 𝒯.deg k) * w ^ (ηa - γa + (ηb - γb))) := by rw [hdd]
        _ ≤ A * B * (d ^ (γ - 𝒯.deg k) * w ^ (η - γ)) :=
            mul_le_mul_of_nonneg_left hkey (mul_nonneg hA hB)
    · rw [hbT j (not_lt.1 hj), abs_zero, mul_zero]
      exact hX
  · rw [haT i (not_lt.1 hi), abs_zero, zero_mul]
    exact hX

end RegularityStructure.GradedProduct

end RegularityStructures

end
