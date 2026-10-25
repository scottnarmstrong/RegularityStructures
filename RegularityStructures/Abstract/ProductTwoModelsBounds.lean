/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductTheorem
public import RegularityStructures.Abstract.Model

/-!
# Coordinate bounds comparing two models

Estimates used in the proof of [Hai14, Proposition 4.10], which compares products of modelled
distributions for two models `(Π, Γ)` and `(Π̄, Γ̄)`:

* `GradedProduct.abs_mul_apply_le_of_rpow`: if `|u_i| ≤ A d^{m − deg i}` (and `u_i = 0` for
  `deg i > m`) and `|v_j| ≤ B d^{n − deg j}` (and `v_j = 0` for `deg j > n`), then
  `|(u ⋆ v)_k| ≤ ‖⋆‖ A B d^{m + n − deg k}`;
* `Model.abs_gammaMap_sub_gammaMap_single_apply_le`:
  `|(Γ_{yx} e_{i'} − Γ̄_{yx} e_{i'})_i| ≤ δ_Γ d(y, x)^{deg i' − deg i}` under
  `GammaDiffBoundOn γ δ_Γ`;
* `Model.abs_gammaMap_homogeneousProj_sub_apply_le`:
  `|(Γ_{yx} Q_m a − Γ̄_{yx} Q_m b)_i| ≤ |ι| (A δ_Γ + δ (1 + C_Γ)) d^{m − deg i}` for `|a| ≤ A`,
  `|a − b| ≤ δ`;
* `Model.abs_mul_gammaMap_sub_mul_gammaMap_apply_le`: the difference of the terms
  `Γ Q_m f₁ ⋆ Γ Q_n f₂` and `Γ̄ Q_m g₁ ⋆ Γ̄ Q_n g₂` of [Hai14, (4.5)].

Source: [Hai14] = arXiv:1303.5113v4, proof of Proposition 4.10.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct)

/-- Product of two vectors with "homogeneous-type" bounds of orders `m` and `n`. -/
theorem abs_mul_apply_le_of_rpow {u v : ι → ℝ} {k : ι} {A B d m n : ℝ} (hd0 : 0 ≤ d)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : ∀ i, 𝒯.deg i ≤ m → |u i| ≤ A * d ^ (m - 𝒯.deg i))
    (hu0 : ∀ i, m < 𝒯.deg i → u i = 0) (hv : ∀ j, 𝒯.deg j ≤ n → |v j| ≤ B * d ^ (n - 𝒯.deg j))
    (hv0 : ∀ j, n < 𝒯.deg j → v j = 0) :
    |P.mul u v k| ≤ P.const * (A * B * d ^ (m + n - 𝒯.deg k)) := by
  have hX : 0 ≤ A * B * d ^ (m + n - 𝒯.deg k) :=
    mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg hd0 _)
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hi : 𝒯.deg i ≤ m
  · by_cases hj : 𝒯.deg j ≤ n
    · have hpow : d ^ (m - 𝒯.deg i) * d ^ (n - 𝒯.deg j) = d ^ (m + n - 𝒯.deg k) := by
        rw [← Real.rpow_add_of_nonneg hd0 (by linarith) (by linarith)]
        congr 1
        linarith
      calc |u i| * |v j| ≤ (A * d ^ (m - 𝒯.deg i)) * (B * d ^ (n - 𝒯.deg j)) :=
            mul_le_mul (hu i hi) (hv j hj) (abs_nonneg _)
              (mul_nonneg hA (Real.rpow_nonneg hd0 _))
        _ = A * B * (d ^ (m - 𝒯.deg i) * d ^ (n - 𝒯.deg j)) := by ring
        _ = A * B * d ^ (m + n - 𝒯.deg k) := by rw [hpow]
    · rw [hv0 j (not_le.1 hj), abs_zero, mul_zero]
      exact hX
  · rw [hu0 i (not_le.1 hi), abs_zero, zero_mul]
    exact hX

end RegularityStructure.GradedProduct

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- `(Γ_{yx} Q_m a − Γ̄_{yx} Q_m b)_i = 0` for `m < deg i`. -/
theorem gammaMap_homogeneousProj_sub_apply_eq_zero (M₁ M₂ : Model 𝒯 K) (x y : E) {m : ℝ}
    (a b : ι → ℝ) {i : ι} (h : m < 𝒯.deg i) :
    M₁.gammaMap y x (homogeneousProj 𝒯.deg m a) i -
      M₂.gammaMap y x (homogeneousProj 𝒯.deg m b) i = 0 := by
  rw [M₁.gammaMap_homogeneousProj_apply_eq_zero x y a h,
    M₂.gammaMap_homogeneousProj_apply_eq_zero x y b h, sub_zero]

end Model

end RegularityStructures

end
