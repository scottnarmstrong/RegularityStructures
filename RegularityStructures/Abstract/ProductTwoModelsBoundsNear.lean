/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductTwoModelsBounds
public import RegularityStructures.Abstract.ProductBoundsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.ProductTwoModelsBounds`

The statements of `RegularityStructures.Abstract.ProductTwoModelsBounds` that involve `Γ`-bounds,
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

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- `|(Γ_{yx} e_{i'})_i − (Γ̄_{yx} e_{i'})_i| ≤ δ_Γ d(y, x)^{deg i' − deg i}` for
`deg i ≤ deg i' < γ`. -/
theorem abs_gammaMap_sub_gammaMap_single_apply_le_near (M₁ M₂ : Model 𝒯 K) {γ δΓ : ℝ} {S : Set E}
    (hΓ : M₁.GammaDiffNearOn M₂ γ δΓ S) (hδΓ : 0 ≤ δΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius)
    {i' i : ι} (hi' : 𝒯.deg i' < γ) (hii' : 𝒯.deg i ≤ 𝒯.deg i') :
    |M₁.gammaMap y x (Pi.single i' 1) i - M₂.gammaMap y x (Pi.single i' 1) i| ≤
      δΓ * K.scaleDist y x ^ (𝒯.deg i' - 𝒯.deg i) := by
  have hd := Real.rpow_nonneg (K.scaleDist_nonneg y x) (𝒯.deg i' - 𝒯.deg i)
  rcases hii'.lt_or_eq with hlt | heq
  · exact hΓ i' i hi' hlt x hx y hy hxy
  · by_cases hii : i = i'
    · subst hii
      rw [(M₁.isGradedUnipotent_gammaMap y x).apply_single_self,
        (M₂.isGradedUnipotent_gammaMap y x).apply_single_self, sub_self, abs_zero]
      exact mul_nonneg hδΓ hd
    · rw [(M₁.isGradedUnipotent_gammaMap y x).apply_single_of_le hii heq.ge,
        (M₂.isGradedUnipotent_gammaMap y x).apply_single_of_le hii heq.ge, sub_self, abs_zero]
      exact mul_nonneg hδΓ hd

/-- `|(Γ_{yx} Q_m a − Γ̄_{yx} Q_m a)_i| ≤ |ι| A δ_Γ d(y, x)^{m − deg i}` for `deg i ≤ m`. -/
theorem abs_gammaMap_sub_gammaMap_homogeneousProj_apply_le_near (M₁ M₂ : Model 𝒯 K)
    {γ δΓ A : ℝ} {S : Set E} (hΓ : M₁.GammaDiffNearOn M₂ γ δΓ S) (hδΓ : 0 ≤ δΓ) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {a : ι → ℝ} (haT : a ∈ lowerSubspace 𝒯.deg γ)
    (ha : ∀ i, |a i| ≤ A) {m : ℝ} {i : ι} (him : 𝒯.deg i ≤ m) :
    |M₁.gammaMap y x (homogeneousProj 𝒯.deg m a) i -
        M₂.gammaMap y x (homogeneousProj 𝒯.deg m a) i| ≤
      Fintype.card ι * (A * δΓ * K.scaleDist y x ^ (m - 𝒯.deg i)) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha i)
  have hX : 0 ≤ A * δΓ * K.scaleDist y x ^ (m - 𝒯.deg i) :=
    mul_nonneg (mul_nonneg hA hδΓ) (Real.rpow_nonneg (K.scaleDist_nonneg y x) _)
  rw [apply_homogeneousProj_apply, apply_homogeneousProj_apply, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i', |(if 𝒯.deg i' = m then a i' else 0) * M₁.gammaMap y x (Pi.single i' 1) i -
      (if 𝒯.deg i' = m then a i' else 0) * M₂.gammaMap y x (Pi.single i' 1) i| ≤
      A * δΓ * K.scaleDist y x ^ (m - 𝒯.deg i) := by
    intro i'
    rw [← mul_sub]
    split_ifs with hi'
    · by_cases hγ : 𝒯.deg i' < γ
      · rw [abs_mul, mul_assoc]
        refine mul_le_mul (ha i') ?_ (abs_nonneg _) hA
        have hii' : 𝒯.deg i ≤ 𝒯.deg i' := by rw [hi']; exact him
        have h := abs_gammaMap_sub_gammaMap_single_apply_le_near M₁ M₂ hΓ hδΓ hx hy hxy hγ hii'
        rwa [hi'] at h
      · rw [haT i' (not_lt.1 hγ), zero_mul, abs_zero]
        exact hX
    · rw [zero_mul, abs_zero]
      exact hX
  calc ∑ i', |(if 𝒯.deg i' = m then a i' else 0) * M₁.gammaMap y x (Pi.single i' 1) i -
        (if 𝒯.deg i' = m then a i' else 0) * M₂.gammaMap y x (Pi.single i' 1) i|
      ≤ ∑ _i' : ι, A * δΓ * K.scaleDist y x ^ (m - 𝒯.deg i) :=
        Finset.sum_le_sum fun i' _ => hterm i'
    _ = Fintype.card ι * (A * δΓ * K.scaleDist y x ^ (m - 𝒯.deg i)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `|(Γ_{yx} Q_m a − Γ̄_{yx} Q_m b)_i| ≤ |ι| (A δ_Γ + δ (1 + C_Γ)) d(y, x)^{m − deg i}` for
`deg i ≤ m`, when `|a| ≤ A`, `|a − b| ≤ δ` and `Γ̄` has bound `C_Γ`. -/
theorem abs_gammaMap_homogeneousProj_sub_apply_le_near (M₁ M₂ : Model 𝒯 K) {γ δΓ CΓ A δ : ℝ}
    {S : Set E} (hΓd : M₁.GammaDiffNearOn M₂ γ δΓ S) (hΓ₂ : M₂.GammaNearOn γ CΓ S)
    (hδΓ : 0 ≤ δΓ) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {a b : ι → ℝ}
    (haT : a ∈ lowerSubspace 𝒯.deg γ) (hbT : b ∈ lowerSubspace 𝒯.deg γ) (ha : ∀ i, |a i| ≤ A)
    (hab : ∀ i, |a i - b i| ≤ δ) {m : ℝ} {i : ι} (him : 𝒯.deg i ≤ m) :
    |M₁.gammaMap y x (homogeneousProj 𝒯.deg m a) i -
        M₂.gammaMap y x (homogeneousProj 𝒯.deg m b) i| ≤
      Fintype.card ι * ((A * δΓ + δ * (1 + CΓ)) * K.scaleDist y x ^ (m - 𝒯.deg i)) := by
  have h1 := abs_gammaMap_sub_gammaMap_homogeneousProj_apply_le_near M₁ M₂ hΓd hδΓ hx hy hxy haT ha him
  have h2 := M₂.abs_gammaMap_homogeneousProj_apply_le_near hΓ₂ hCΓ hx hy hxy
    (Submodule.sub_mem _ haT hbT) (a := a - b) hab him
  have hsplit : M₁.gammaMap y x (homogeneousProj 𝒯.deg m a) i -
      M₂.gammaMap y x (homogeneousProj 𝒯.deg m b) i =
      (M₁.gammaMap y x (homogeneousProj 𝒯.deg m a) i -
        M₂.gammaMap y x (homogeneousProj 𝒯.deg m a) i) +
      M₂.gammaMap y x (homogeneousProj 𝒯.deg m (a - b)) i := by
    rw [map_sub, map_sub, Pi.sub_apply]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring

/-- The difference of the terms of [Hai14, (4.5)] for two models:
`|(Γ Q_m a₁ ⋆ Γ Q_n a₂ − Γ̄ Q_m b₁ ⋆ Γ̄ Q_n b₂)_k| ≤ ‖⋆‖ |ι|² B d(y, x)^{m + n − deg k}` with
`B = (C₁ δ_Γ + δ₁ (1 + C_Γ)) C₂ (1 + C_Γ) + C₁ (1 + C_Γ) (C₂ δ_Γ + δ₂ (1 + C_Γ))`. -/
theorem abs_mul_gammaMap_sub_mul_gammaMap_apply_le_near (M₁ M₂ : Model 𝒯 K)
    (P : 𝒯.GradedProduct) {γ₁ γ₂ δΓ CΓ C₁ C₂ δ₁ δ₂ : ℝ} {S : Set E}
    (hΓd₁ : M₁.GammaDiffNearOn M₂ γ₁ δΓ S) (hΓd₂ : M₁.GammaDiffNearOn M₂ γ₂ δΓ S)
    (hΓ₁ : M₁.GammaNearOn γ₂ CΓ S) (hΓ₂ : M₂.GammaNearOn γ₁ CΓ S)
    (hΓ₂' : M₂.GammaNearOn γ₂ CΓ S) (hδΓ : 0 ≤ δΓ) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S)
    (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {a₁ a₂ b₁ b₂ : ι → ℝ} (ha₁T : a₁ ∈ lowerSubspace 𝒯.deg γ₁)
    (hb₁T : b₁ ∈ lowerSubspace 𝒯.deg γ₁) (ha₂T : a₂ ∈ lowerSubspace 𝒯.deg γ₂)
    (hb₂T : b₂ ∈ lowerSubspace 𝒯.deg γ₂) (ha₁ : ∀ i, |a₁ i| ≤ C₁) (hb₁ : ∀ i, |b₁ i| ≤ C₁)
    (ha₂ : ∀ i, |a₂ i| ≤ C₂) (hab₁ : ∀ i, |a₁ i - b₁ i| ≤ δ₁)
    (hab₂ : ∀ i, |a₂ i - b₂ i| ≤ δ₂) (m n : ℝ) (k : ι) :
    |P.mul (M₁.gammaMap y x (homogeneousProj 𝒯.deg m a₁))
          (M₁.gammaMap y x (homogeneousProj 𝒯.deg n a₂)) k -
        P.mul (M₂.gammaMap y x (homogeneousProj 𝒯.deg m b₁))
          (M₂.gammaMap y x (homogeneousProj 𝒯.deg n b₂)) k| ≤
      P.const * ((Fintype.card ι : ℝ) ^ 2 *
        ((C₁ * δΓ + δ₁ * (1 + CΓ)) * (C₂ * (1 + CΓ)) +
          C₁ * (1 + CΓ) * (C₂ * δΓ + δ₂ * (1 + CΓ))) * K.scaleDist y x ^ (m + n - 𝒯.deg k)) := by
  have hd0 := K.scaleDist_nonneg y x
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (ha₁ k)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (ha₂ k)
  have hδ₁ : 0 ≤ δ₁ := (abs_nonneg _).trans (hab₁ k)
  have hδ₂ : 0 ≤ δ₂ := (abs_nonneg _).trans (hab₂ k)
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  set u₁ := M₁.gammaMap y x (homogeneousProj 𝒯.deg m a₁)
  set v₁ := M₁.gammaMap y x (homogeneousProj 𝒯.deg n a₂)
  set u₂ := M₂.gammaMap y x (homogeneousProj 𝒯.deg m b₁)
  set v₂ := M₂.gammaMap y x (homogeneousProj 𝒯.deg n b₂)
  have hsplit : P.mul u₁ v₁ k - P.mul u₂ v₂ k = P.mul (u₁ - u₂) v₁ k + P.mul u₂ (v₁ - v₂) k := by
    simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply]
    ring
  -- the first factor difference
  have hT1 := P.abs_mul_apply_le_of_rpow (u := u₁ - u₂) (v := v₁) (k := k) hd0
    (A := Fintype.card ι * (C₁ * δΓ + δ₁ * (1 + CΓ)))
    (B := Fintype.card ι * (C₂ * (1 + CΓ))) (m := m) (n := n)
    (mul_nonneg hN (add_nonneg (mul_nonneg hC₁ hδΓ) (mul_nonneg hδ₁ (by linarith))))
    (mul_nonneg hN (mul_nonneg hC₂ (by linarith)))
    (fun i hi => by
      have h := abs_gammaMap_homogeneousProj_sub_apply_le_near M₁ M₂ hΓd₁ hΓ₂ hδΓ hCΓ hx hy hxy ha₁T
        hb₁T ha₁ hab₁ hi
      rw [Pi.sub_apply]
      refine h.trans (le_of_eq ?_)
      ring)
    (fun i hi => by
      rw [Pi.sub_apply]
      exact gammaMap_homogeneousProj_sub_apply_eq_zero M₁ M₂ x y a₁ b₁ hi)
    (fun j hj => by
      have h := M₁.abs_gammaMap_homogeneousProj_apply_le_near hΓ₁ hCΓ hx hy hxy ha₂T ha₂ hj
      refine h.trans (le_of_eq ?_)
      ring)
    (fun j hj => M₁.gammaMap_homogeneousProj_apply_eq_zero x y a₂ hj)
  -- the second factor difference
  have hT2 := P.abs_mul_apply_le_of_rpow (u := u₂) (v := v₁ - v₂) (k := k) hd0
    (A := Fintype.card ι * (C₁ * (1 + CΓ)))
    (B := Fintype.card ι * (C₂ * δΓ + δ₂ * (1 + CΓ))) (m := m) (n := n)
    (mul_nonneg hN (mul_nonneg hC₁ (by linarith)))
    (mul_nonneg hN (add_nonneg (mul_nonneg hC₂ hδΓ) (mul_nonneg hδ₂ (by linarith))))
    (fun i hi => by
      have h := M₂.abs_gammaMap_homogeneousProj_apply_le_near hΓ₂ hCΓ hx hy hxy hb₁T hb₁ hi
      refine h.trans (le_of_eq ?_)
      ring)
    (fun i hi => M₂.gammaMap_homogeneousProj_apply_eq_zero x y b₁ hi)
    (fun j hj => by
      have h := abs_gammaMap_homogeneousProj_sub_apply_le_near M₁ M₂ hΓd₂ hΓ₂' hδΓ hCΓ hx hy hxy ha₂T
        hb₂T ha₂ hab₂ hj
      rw [Pi.sub_apply]
      refine h.trans (le_of_eq ?_)
      ring)
    (fun j hj => by
      rw [Pi.sub_apply]
      exact gammaMap_homogeneousProj_sub_apply_eq_zero M₁ M₂ x y a₂ b₂ hj)
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add hT1 hT2).trans (le_of_eq ?_))
  ring

end Model

end RegularityStructures

end
