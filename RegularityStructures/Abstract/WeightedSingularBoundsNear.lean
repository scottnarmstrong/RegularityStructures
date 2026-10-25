/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularBounds
public import RegularityStructures.Abstract.ProductBoundsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.WeightedSingularBounds`

The statements of `RegularityStructures.Abstract.WeightedSingularBounds` that involve `Γ`-bounds,
for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct)

end RegularityStructure.GradedProduct

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- The bound (6.12) of [Hai14] on the terms `Γ Q_m a ⋆ Γ Q_n b` with `m + n ≥ γ`, for
`|a_i| ≤ C₁ w^{(η₁ − deg i) ∧ 0}` (zero below `α₁`), `|b_j| ≤ C₂ w^{(η₂ − deg j) ∧ 0}` (zero
below `α₂`), and `η ≤ (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)`, `η ≤ γ`. -/
theorem abs_mul_gammaMap_homogeneousProj_apply_le_weighted_near (P : 𝒯.GradedProduct)
    {γ₁ γ₂ α₁ α₂ η₁ η₂ γ η CΓ C₁ C₂ w : ℝ} {S : Set E} (hΓ₁ : M.GammaNearOn γ₁ CΓ S)
    (hΓ₂ : M.GammaNearOn γ₂ CΓ S) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hdw : K.scaleDist y x ≤ w) (hw0 : 0 < w) (hw1 : w ≤ 1) {a b : ι → ℝ}
    (haT : a ∈ lowerSubspace 𝒯.deg γ₁) (hbT : b ∈ lowerSubspace 𝒯.deg γ₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (ha : ∀ i, |a i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0)
    (hb : ∀ j, |b j| ≤ C₂ * w ^ min (η₂ - 𝒯.deg j) 0) (haα : ∀ i, 𝒯.deg i < α₁ → a i = 0)
    (hbα : ∀ j, 𝒯.deg j < α₂ → b j = 0) (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁)
    (hη₁₂ : η ≤ η₁ + η₂) (hηγ : η ≤ γ) {m n : ℝ} (hmn : γ ≤ m + n) {k : ι}
    (hk : 𝒯.deg k < γ) :
    |P.mul (M.gammaMap y x (homogeneousProj 𝒯.deg m a))
        (M.gammaMap y x (homogeneousProj 𝒯.deg n b)) k| ≤
      P.const * ((Fintype.card ι * (C₁ * (1 + CΓ))) * (Fintype.card ι * (C₂ * (1 + CΓ))) *
        (K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ))) := by
  have hd0 := K.scaleDist_nonneg y x
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hX : 0 ≤ P.const * ((Fintype.card ι * (C₁ * (1 + CΓ))) *
      (Fintype.card ι * (C₂ * (1 + CΓ))) * (K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ))) :=
    mul_nonneg P.const_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hN (mul_nonneg hC₁
      (by linarith))) (mul_nonneg hN (mul_nonneg hC₂ (by linarith))))
      (mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)))
  -- vanishing of `Q_m a` for `m < α₁` and of `Q_n b` for `n < α₂`
  by_cases hm : m < α₁
  · have h0 : homogeneousProj 𝒯.deg m a = 0 := by
      funext i
      rw [homogeneousProj_apply, Pi.zero_apply]
      split_ifs with h
      · exact haα i (h ▸ hm)
      · rfl
    rw [h0, map_zero, map_zero, LinearMap.zero_apply, Pi.zero_apply, abs_zero]
    exact hX
  by_cases hn : n < α₂
  · have h0 : homogeneousProj 𝒯.deg n b = 0 := by
      funext j
      rw [homogeneousProj_apply, Pi.zero_apply]
      split_ifs with h
      · exact hbα j (h ▸ hn)
      · rfl
    rw [h0, map_zero, map_zero, Pi.zero_apply, abs_zero]
    exact hX
  -- the homogeneous parts and their bounds
  set A : ℝ := C₁ * w ^ min (η₁ - m) 0 with hA_def
  set B : ℝ := C₂ * w ^ min (η₂ - n) 0 with hB_def
  have hQa : ∀ i, |homogeneousProj 𝒯.deg m a i| ≤ A := by
    intro i
    rw [homogeneousProj_apply]
    split_ifs with h
    · rw [hA_def, ← h]
      exact ha i
    · rw [abs_zero]
      exact mul_nonneg hC₁ (Real.rpow_nonneg hw0.le _)
  have hQb : ∀ j, |homogeneousProj 𝒯.deg n b j| ≤ B := by
    intro j
    rw [homogeneousProj_apply]
    split_ifs with h
    · rw [hB_def, ← h]
      exact hb j
    · rw [abs_zero]
      exact mul_nonneg hC₂ (Real.rpow_nonneg hw0.le _)
  have hQaT : homogeneousProj 𝒯.deg m a ∈ lowerSubspace 𝒯.deg γ₁ := fun i hi => by
    rw [homogeneousProj_apply, haT i hi, ite_self]
  have hQbT : homogeneousProj 𝒯.deg n b ∈ lowerSubspace 𝒯.deg γ₂ := fun j hj => by
    rw [homogeneousProj_apply, hbT j hj, ite_self]
  have h := M.abs_mul_gammaMap_homogeneousProj_apply_le_near P hΓ₁ hΓ₂ hCΓ hx hy
    (le_gammaNearRadius_of_le_one (hdw.trans hw1)) hQaT hQbT hQa hQb
    m n k
  rw [homogeneousProj_eq_self (homogeneousProj_mem _ _ _),
    homogeneousProj_eq_self (homogeneousProj_mem _ _ _)] at h
  refine h.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (rpow_mul_rpow_le_rpow_mul_rpow (a := m + n - 𝒯.deg k)
      (b := min (η₁ - m) 0 + min (η₂ - n) 0) hd0 hdw hw0 hw1 (by linarith) (by linarith) ?_)
    (mul_nonneg (mul_nonneg hN (mul_nonneg hC₁ (by linarith)))
      (mul_nonneg hN (mul_nonneg hC₂ (by linarith))))) P.const_nonneg))
  · rw [hA_def, hB_def, Real.rpow_add hw0]
    ring
  · have hm' := not_lt.1 hm
    have hn' := not_lt.1 hn
    rcases min_cases (η₁ - m) 0 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases min_cases (η₂ - n) 0 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> linarith

end Model

end RegularityStructures

end
