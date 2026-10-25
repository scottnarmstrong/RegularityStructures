/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.QFamilyModelBound

/-!
# Local order of the model on a ball, near-pair `Γ`-bounds

A termwise bound on `Γ_{yx} e_i` combined with `Q_u Π_y e_j` for `d(y, x) ≤ gammaNearRadius`, and
the local order on a ball inside `S`: for `x ∈ S`, `0 < u ≤ 1`, `R ≤ gammaNearRadius` and
`{d(·, x) ≤ R} ⊆ S`,
`|(Q_u Π_x e_i)(y)| ≤ |ι| max(1, C_Γ) C_Π ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
  (M : Model 𝒯 K) {γ CPi CGam : ℝ} {S : Set E}

theorem abs_gammaMap_mul_regPi_le_of_mem_near (hPi : M.PiBoundOn γ CPi S) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam S) {i : ι} (hi : 𝒯.deg i < γ) {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) (j : ι) :
    |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| ≤
      if 𝒯.deg j ≤ 𝒯.deg i then
        max 1 CGam * CPi * (u ^ (𝒯.deg j / K.order) * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
      else 0 := by
  have hC1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
  have hR : 0 ≤ max 1 CGam * CPi *
      (u ^ (𝒯.deg j / K.order) * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) :=
    mul_nonneg (mul_nonneg hC1 hCPi)
      (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
  by_cases hji : j = i
  · subst hji
    simp only [le_refl, ↓reduceIte]
    rw [M.gammaMap_single_apply_self, one_mul, sub_self, Real.rpow_zero, mul_one]
    calc |M.regPi y (Pi.single j 1) u y| ≤ CPi * u ^ (𝒯.deg j / K.order) :=
          hPi j hi u hu y hy
      _ = 1 * CPi * u ^ (𝒯.deg j / K.order) := by ring
      _ ≤ max 1 CGam * CPi * u ^ (𝒯.deg j / K.order) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hCPi)
            (Real.rpow_nonneg hu.1.le _)
  · by_cases hlt : 𝒯.deg j < 𝒯.deg i
    · simp only [hlt.le, ↓reduceIte]
      rw [abs_mul]
      have hG := hGam i j hi hlt x hx y hy hxy
      have hP := hPi j (hlt.trans hi) u hu y hy
      calc |M.gammaMap y x (Pi.single i 1) j| * |M.regPi y (Pi.single j 1) u y|
          ≤ (max 1 CGam * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) *
              (CPi * u ^ (𝒯.deg j / K.order)) :=
            mul_le_mul (hG.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))) hP (abs_nonneg _)
              (mul_nonneg hC1 (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
        _ = _ := by ring
    · rw [M.gammaMap_single_apply_of_le x y hji (not_lt.1 hlt), zero_mul, abs_zero]
      split_ifs
      · exact hR
      · exact le_rfl

/-- **Local order on a ball inside `S`**: for `x ∈ S`, `0 < u ≤ 1` and `d(y, x) ≤ R` with the
ball `{d(·, x) ≤ R} ⊆ S`,
`|(Q_u Π_x e_i)(y)| ≤ |ι| max(1, C_Γ) C_Π ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`. -/
theorem abs_regPi_single_le_of_ball_near (hPi : M.PiBoundOn γ CPi S) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam S) {i : ι} (hi : 𝒯.deg i < γ) {x : E} (hx : x ∈ S) {R : ℝ} (hR : R ≤ gammaNearRadius)
    (hball : ∀ y, K.scaleDist y x ≤ R → y ∈ S) :
    ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x ≤ R →
      |M.regPi x (Pi.single i 1) u y| ≤ Fintype.card ι * (max 1 CGam * CPi) *
        ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i), u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
  intro u hu y hyR
  have hy : y ∈ S := hball y hyR
  have hC1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
  set T := Finset.univ.filter (fun j => 𝒯.deg j ≤ 𝒯.deg i) with hT
  set h : ℝ → ℝ := fun a =>
    max 1 CGam * CPi * (u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a)) with hh
  have hh0 : ∀ a ∈ T.image 𝒯.deg, 0 ≤ h a := fun a _ =>
    mul_nonneg (mul_nonneg hC1 hCPi)
      (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
  calc |M.regPi x (Pi.single i 1) u y|
      = |∑ j, M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| := by
        rw [← M.regPi_gammaMap y x, M.regPi_eq_sum]
    _ ≤ ∑ j, |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, if 𝒯.deg j ≤ 𝒯.deg i then h (𝒯.deg j) else 0 :=
        Finset.sum_le_sum fun j _ => M.abs_gammaMap_mul_regPi_le_of_mem_near hPi hCPi hGam hi hu hx hy (hyR.trans hR) j
    _ = ∑ j ∈ T, h (𝒯.deg j) := by rw [hT, Finset.sum_filter]
    _ ≤ Fintype.card ι * ∑ a ∈ T.image 𝒯.deg, h a := sum_le_card_mul_sum_image 𝒯 T hh0
    _ = Fintype.card ι * (max 1 CGam * CPi) * ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i),
          u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
        rw [RegularityStructure.degreesAtMost, ← hT, hh, ← Finset.mul_sum]
        ring

end Model

end RegularityStructures

end
