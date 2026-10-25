/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductBounds
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.ProductBounds`

The statements of `RegularityStructures.Abstract.ProductBounds` that involve `Γ`-bounds, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
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

/-- `|(Γ_{yx} e_{i'})_i| ≤ (1 + C_Γ) d(y, x)^{deg i' − deg i}` for `deg i ≤ deg i' < γ`. -/
theorem abs_gammaMap_single_apply_le_near {γ CΓ : ℝ} {S : Set E} (hΓ : M.GammaNearOn γ CΓ S)
    (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {i' i : ι} (hi' : 𝒯.deg i' < γ)
    (hii' : 𝒯.deg i ≤ 𝒯.deg i') :
    |M.gammaMap y x (Pi.single i' 1) i| ≤
      (1 + CΓ) * K.scaleDist y x ^ (𝒯.deg i' - 𝒯.deg i) := by
  have hd := Real.rpow_nonneg (K.scaleDist_nonneg y x) (𝒯.deg i' - 𝒯.deg i)
  rcases hii'.lt_or_eq with hlt | heq
  · exact (hΓ i' i hi' hlt x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right (by linarith) hd)
  · by_cases hii : i = i'
    · subst hii
      rw [(M.isGradedUnipotent_gammaMap y x).apply_single_self, sub_self, Real.rpow_zero,
        abs_one, mul_one]
      linarith
    · rw [(M.isGradedUnipotent_gammaMap y x).apply_single_of_le hii heq.ge, abs_zero]
      exact mul_nonneg (by linarith) hd

/-- `|(Γ_{yx} Q_m a)_i| ≤ |ι| A (1 + C_Γ) d(y, x)^{m − deg i}` for `deg i ≤ m`, when
`a ∈ T_{<γ}` and `|a_{i'}| ≤ A`. -/
theorem abs_gammaMap_homogeneousProj_apply_le_near {γ CΓ A : ℝ} {S : Set E}
    (hΓ : M.GammaNearOn γ CΓ S) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {a : ι → ℝ} (haT : a ∈ lowerSubspace 𝒯.deg γ) (ha : ∀ i, |a i| ≤ A) {m : ℝ} {i : ι}
    (him : 𝒯.deg i ≤ m) :
    |M.gammaMap y x (homogeneousProj 𝒯.deg m a) i| ≤
      Fintype.card ι * (A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i)) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha i)
  have hX : 0 ≤ A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i) :=
    mul_nonneg (mul_nonneg hA (by linarith)) (Real.rpow_nonneg (K.scaleDist_nonneg y x) _)
  rw [apply_homogeneousProj_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i', |(if 𝒯.deg i' = m then a i' else 0) * M.gammaMap y x (Pi.single i' 1) i|
      ≤ A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i) := by
    intro i'
    split_ifs with hi'
    · by_cases hγ : 𝒯.deg i' < γ
      · rw [abs_mul, mul_assoc]
        refine mul_le_mul (ha i') ?_ (abs_nonneg _) hA
        have hii' : 𝒯.deg i ≤ 𝒯.deg i' := by rw [hi']; exact him
        have h := M.abs_gammaMap_single_apply_le_near hΓ hCΓ hx hy hxy hγ hii'
        rwa [hi'] at h
      · rw [haT i' (not_lt.1 hγ), zero_mul, abs_zero]
        exact hX
    · rw [zero_mul, abs_zero]
      exact hX
  calc ∑ i', |(if 𝒯.deg i' = m then a i' else 0) * M.gammaMap y x (Pi.single i' 1) i|
      ≤ ∑ _i' : ι, A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i) :=
        Finset.sum_le_sum fun i' _ => hterm i'
    _ = Fintype.card ι * (A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The bound behind [Hai14, (4.6)]:
`|(Γ_{yx} Q_m a ⋆ Γ_{yx} Q_n b)_k| ≤ ‖⋆‖ (|ι| A (1 + C_Γ)) (|ι| B (1 + C_Γ))`
`· d(y, x)^{m + n − deg k}`
for `a ∈ T_{<γ_a}`, `b ∈ T_{<γ_b}` with `|a| ≤ A`, `|b| ≤ B` coordinatewise. -/
theorem abs_mul_gammaMap_homogeneousProj_apply_le_near (P : 𝒯.GradedProduct) {γa γb CΓ A B : ℝ}
    {S : Set E} (hΓa : M.GammaNearOn γa CΓ S) (hΓb : M.GammaNearOn γb CΓ S) (hCΓ : 0 ≤ CΓ)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {a b : ι → ℝ} (haT : a ∈ lowerSubspace 𝒯.deg γa)
    (hbT : b ∈ lowerSubspace 𝒯.deg γb) (ha : ∀ i, |a i| ≤ A) (hb : ∀ j, |b j| ≤ B)
    (m n : ℝ) (k : ι) :
    |P.mul (M.gammaMap y x (homogeneousProj 𝒯.deg m a))
        (M.gammaMap y x (homogeneousProj 𝒯.deg n b)) k| ≤
      P.const * ((Fintype.card ι * (A * (1 + CΓ))) * (Fintype.card ι * (B * (1 + CΓ))) *
        K.scaleDist y x ^ (m + n - 𝒯.deg k)) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha k)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb k)
  have hd0 := K.scaleDist_nonneg y x
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hNA : 0 ≤ (Fintype.card ι : ℝ) * (A * (1 + CΓ)) :=
    mul_nonneg hN (mul_nonneg hA (by linarith))
  have hNB : 0 ≤ (Fintype.card ι : ℝ) * (B * (1 + CΓ)) :=
    mul_nonneg hN (mul_nonneg hB (by linarith))
  have hX : 0 ≤ (Fintype.card ι * (A * (1 + CΓ))) * (Fintype.card ι * (B * (1 + CΓ))) *
      K.scaleDist y x ^ (m + n - 𝒯.deg k) :=
    mul_nonneg (mul_nonneg hNA hNB) (Real.rpow_nonneg hd0 _)
  refine P.abs_mul_apply_le hX fun i j hij => ?_
  by_cases hi : 𝒯.deg i ≤ m
  · by_cases hj : 𝒯.deg j ≤ n
    · have h1 := M.abs_gammaMap_homogeneousProj_apply_le_near hΓa hCΓ hx hy hxy haT ha hi
      have h2 := M.abs_gammaMap_homogeneousProj_apply_le_near hΓb hCΓ hx hy hxy hbT hb hj
      have hpow : K.scaleDist y x ^ (m - 𝒯.deg i) * K.scaleDist y x ^ (n - 𝒯.deg j) =
          K.scaleDist y x ^ (m + n - 𝒯.deg k) := by
        rw [← Real.rpow_add_of_nonneg hd0 (by linarith) (by linarith)]
        congr 1
        linarith
      calc _ ≤ (Fintype.card ι * (A * (1 + CΓ) * K.scaleDist y x ^ (m - 𝒯.deg i))) *
            (Fintype.card ι * (B * (1 + CΓ) * K.scaleDist y x ^ (n - 𝒯.deg j))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hN (mul_nonneg (mul_nonneg hA
              (by linarith)) (Real.rpow_nonneg hd0 _)))
        _ = (Fintype.card ι * (A * (1 + CΓ))) * (Fintype.card ι * (B * (1 + CΓ))) *
            (K.scaleDist y x ^ (m - 𝒯.deg i) * K.scaleDist y x ^ (n - 𝒯.deg j)) := by ring
        _ = _ := by rw [hpow]
    · rw [M.gammaMap_homogeneousProj_apply_eq_zero x y b (not_le.1 hj), abs_zero, mul_zero]
      exact hX
  · rw [M.gammaMap_homogeneousProj_apply_eq_zero x y a (not_le.1 hi), abs_zero, zero_mul]
    exact hX

end Model

end RegularityStructures

end
