/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularProduct
public import RegularityStructures.Abstract.WeightedSingularBoundsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.WeightedSingularProduct`

The statements of `RegularityStructures.Abstract.WeightedSingularProduct` that involve `Γ`-bounds,
for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

variable (P : 𝒯.GradedProduct)

/-- The increment of `f₁ ⋆_γ f₂` for an admissible pair of points [Hai14, proof of
Proposition 6.12]. -/
theorem abs_truncMul_increment_le_singular_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α₁ α₂ γ₁ γ₂ γ η₁ η₂ η : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α₁)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W α₂) (hγ₁ : γ ≤ γ₁ + α₂)
    (hγ₂ : γ ≤ γ₂ + α₁) (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂)
    (hηγ : η ≤ γ) (hreg : P.IsRegularPair V W γ) {ρ : E → ℝ} {S : Set E}
    {f₁ f₂ : E → ι → ℝ} {C₁ C₂ CΓ : ℝ} (hf₁V : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ V)
    (hf₂W : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ W)
    (hf₁T : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hf₂T : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hf₁ : M.SingularBoundOn ρ γ₁ η₁ C₁ S f₁) (hf₂ : M.SingularBoundOn ρ γ₂ η₂ C₂ S f₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hΓ₁ : M.GammaNearOn γ₁ CΓ S)
    (hΓ₂ : M.GammaNearOn γ₂ CΓ S) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hρx : 0 < ρ x) (hρy : 0 < ρ y)
    (hd : K.scaleDist y x ≤ min (singularWeight ρ x) (singularWeight ρ y)) {k : ι}
    (hk : 𝒯.deg k < γ) :
    |(P.truncMul γ f₁ f₂ y - M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k| ≤
      P.truncMulConst * C₁ * C₂ * (1 + CΓ) ^ 2 * K.scaleDist y x ^ (γ - 𝒯.deg k) *
        min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ) := by
  set w := min (singularWeight ρ x) (singularWeight ρ y) with hw_def
  have hw0 : 0 < w := lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one ρ x)
  have hd0 : 0 ≤ K.scaleDist y x := K.scaleDist_nonneg y x
  have hF := P.lowerProj_mul_sub_map_apply_eq (M.gammaMap y x) (f₁ x) (f₂ x) (f₁ y) (f₂ y) hk
  have hdec : (P.truncMul γ f₁ f₂ y - M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k =
      P.mul (f₁ y) (f₂ y - M.gammaMap y x (f₂ x)) k +
        P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y) k -
        P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y - M.gammaMap y x (f₂ x)) k +
        (P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
          M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k := hF
  -- coordinate facts
  have hf₁y : ∀ i, |f₁ y i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0 :=
    hf₁.abs_apply_le_weight M hC₁ (hf₁T y hy hρy) hy hρy hw0 (min_le_right _ _)
  have hf₂y : ∀ j, |f₂ y j| ≤ C₂ * w ^ min (η₂ - 𝒯.deg j) 0 :=
    hf₂.abs_apply_le_weight M hC₂ (hf₂T y hy hρy) hy hρy hw0 (min_le_right _ _)
  have hf₁x : ∀ i, |f₁ x i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0 :=
    hf₁.abs_apply_le_weight M hC₁ (hf₁T x hx hρx) hx hρx hw0 (min_le_left _ _)
  have hf₂x : ∀ j, |f₂ x j| ≤ C₂ * w ^ min (η₂ - 𝒯.deg j) 0 :=
    hf₂.abs_apply_le_weight M hC₂ (hf₂T x hx hρx) hx hρx hw0 (min_le_left _ _)
  have hf₁yα : ∀ i, 𝒯.deg i < α₁ → f₁ y i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα (hf₁V y hy hρy) hi
  have hf₂yα : ∀ j, 𝒯.deg j < α₂ → f₂ y j = 0 := fun j hj =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα (hf₂W y hy hρy) hj
  have hf₁xα : ∀ i, 𝒯.deg i < α₁ → f₁ x i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα (hf₁V x hx hρx) hi
  have hf₂xα : ∀ j, 𝒯.deg j < α₂ → f₂ x j = 0 := fun j hj =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα (hf₂W x hx hρx) hj
  have hD₁ : ∀ i, 𝒯.deg i < γ₁ → |(f₁ y - M.gammaMap y x (f₁ x)) i| ≤
      C₁ * K.scaleDist y x ^ (γ₁ - 𝒯.deg i) * w ^ (η₁ - γ₁) := fun i hi =>
    hf₁.2 x hx y hy hρx hρy hd i hi
  have hD₂ : ∀ j, 𝒯.deg j < γ₂ → |(f₂ y - M.gammaMap y x (f₂ x)) j| ≤
      C₂ * K.scaleDist y x ^ (γ₂ - 𝒯.deg j) * w ^ (η₂ - γ₂) := fun j hj =>
    hf₂.2 x hx y hy hρx hρy hd j hj
  have hD₁T : ∀ i, γ₁ ≤ 𝒯.deg i → (f₁ y - M.gammaMap y x (f₁ x)) i = 0 := fun i hi =>
    M.increment_apply_eq_zero_of_mem (hf₁T x hx hρx) (hf₁T y hy hρy) hi
  have hD₂T : ∀ j, γ₂ ≤ 𝒯.deg j → (f₂ y - M.gammaMap y x (f₂ x)) j = 0 := fun j hj =>
    M.increment_apply_eq_zero_of_mem (hf₂T x hx hρx) (hf₂T y hy hρy) hj
  have hD₁α : ∀ i, 𝒯.deg i < α₁ → (f₁ y - M.gammaMap y x (f₁ x)) i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
      (M.increment_mem_of_mem hV (hf₁V x hx hρx) (hf₁V y hy hρy)) hi
  -- the three terms of (4.4)
  have hT1 := P.abs_mul_apply_le_of_right_increment_weighted hd0 hd hw0 hw1 hk hγ₂ hη₁₂
    (by linarith) hC₁ hC₂ hf₁y hf₁yα hD₂ hD₂T
  have hT2 := P.abs_mul_apply_le_of_left_increment_weighted hd0 hd hw0 hw1 hk hγ₁ hη₁₂ hη₁
    hC₁ hC₂ hD₁ hD₁T hf₂y hf₂yα
  have hT3 := P.abs_mul_apply_le_of_increments_weighted hd0 hd hw0 hw1 hk hγ₂ hη₁₂ hC₁ hC₂ hD₁
    hD₁T hD₁α hD₂ hD₂T
  -- the remainder (4.5)–(4.6), (6.12)
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set V₀ : ℝ := K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ) with hV₀_def
  have hV₀ : 0 ≤ V₀ := mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)
  set X : ℝ := P.const * ((N * (C₁ * (1 + CΓ))) * (N * (C₂ * (1 + CΓ))) * V₀) with hX_def
  have hX : 0 ≤ X := mul_nonneg P.const_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hN (mul_nonneg hC₁ (by linarith))) (mul_nonneg hN (mul_nonneg hC₂
    (by linarith)))) hV₀)
  have hR : |(P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
      M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k| ≤ N * (N * X) := by
    rw [M.mul_gammaMap_sub_gammaMap_truncMul_eq P hV hW hreg (hf₁V x hx hρx)
      (hf₂W x hx hρx) y]
    refine abs_sum_sum_image_apply_le 𝒯.deg _ k hX fun m _ n _ => ?_
    split_ifs with hmn
    · rw [Pi.zero_apply, abs_zero]
      exact hX
    · exact M.abs_mul_gammaMap_homogeneousProj_apply_le_weighted_near P hΓ₁ hΓ₂ hCΓ hx hy hd hw0
        hw1 (hf₁T x hx hρx) (hf₂T x hx hρx) hC₁ hC₂ hf₁x hf₂x hf₁xα hf₂xα hη₁ hη₂ hη₁₂ hηγ
        (not_lt.1 hmn) hk
  -- assembly
  set Z : ℝ := P.const * C₁ * C₂ * V₀ with hZ_def
  have hZ : 0 ≤ Z := mul_nonneg (mul_nonneg (mul_nonneg P.const_nonneg hC₁) hC₂) hV₀
  have hG : 1 ≤ (1 + CΓ) ^ 2 := one_le_pow₀ (by linarith)
  have hNX : N * (N * X) = N ^ 4 * (Z * (1 + CΓ) ^ 2) := by
    rw [hX_def, hZ_def]
    ring
  have hTZ : P.const * (C₁ * C₂ * V₀) = Z := by
    rw [hZ_def]
    ring
  rw [hdec]
  calc _ ≤ |P.mul (f₁ y) (f₂ y - M.gammaMap y x (f₂ x)) k| +
        |P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y) k| +
        |P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y - M.gammaMap y x (f₂ x)) k| +
        |(P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
          M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k| := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le (P.mul (f₁ y) (f₂ y - M.gammaMap y x (f₂ x)) k),
          le_abs_self (P.mul (f₁ y) (f₂ y - M.gammaMap y x (f₂ x)) k),
          neg_abs_le (P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y) k),
          le_abs_self (P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y) k),
          neg_abs_le (P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y - M.gammaMap y x (f₂ x)) k),
          le_abs_self (P.mul (f₁ y - M.gammaMap y x (f₁ x)) (f₂ y - M.gammaMap y x (f₂ x)) k),
          neg_abs_le ((P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
            M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k),
          le_abs_self ((P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
            M.gammaMap y x (P.truncMul γ f₁ f₂ x)) k)]
    _ ≤ Z + Z + Z + N ^ 4 * (Z * (1 + CΓ) ^ 2) := by
        rw [← hNX, ← hTZ]
        linarith
    _ ≤ (3 + N ^ 4) * (Z * (1 + CΓ) ^ 2) := three_add_card_pow_le hZ hG
    _ = _ := by
        rw [hZ_def, hV₀_def, RegularityStructure.GradedProduct.truncMulConst]
        ring

/-- **Multiplication of singular modelled distributions** [Hai14, Proposition 6.12], bound on a
set `S`, for every `γ ≤ (γ₁ + α₂) ∧ (γ₂ + α₁)` and `η ≤ (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)` with
`η ≤ γ` (see the module docstring for why `η ≤ γ` is needed):
`|||f₁ ⋆_γ f₂|||_{γ,η;S} ≤ c C₁ C₂ (1 + C_Γ)²` with `c = (3 + |ι|⁴) ‖⋆‖`. -/
theorem singularBoundOn_truncMul_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α₁ α₂ γ₁ γ₂ γ η₁ η₂ η : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α₁)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W α₂) (hγ₁ : γ ≤ γ₁ + α₂)
    (hγ₂ : γ ≤ γ₂ + α₁) (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂)
    (hηγ : η ≤ γ) (hreg : P.IsRegularPair V W γ) {ρ : E → ℝ} {S : Set E}
    {f₁ f₂ : E → ι → ℝ} {C₁ C₂ CΓ : ℝ} (hf₁V : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ V)
    (hf₂W : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ W)
    (hf₁T : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hf₂T : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hf₁ : M.SingularBoundOn ρ γ₁ η₁ C₁ S f₁) (hf₂ : M.SingularBoundOn ρ γ₂ η₂ C₂ S f₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hΓ₁ : M.GammaNearOn γ₁ CΓ S)
    (hΓ₂ : M.GammaNearOn γ₂ CΓ S) (hCΓ : 0 ≤ CΓ) :
    M.SingularBoundOn ρ γ η (P.truncMulConst * C₁ * C₂ * (1 + CΓ) ^ 2) S
      (P.truncMul γ f₁ f₂) := by
  refine ⟨fun x hx hρ k _ => ?_, fun x hx y hy hρx hρy hd k hk => ?_⟩
  · have hw0 := singularWeight_pos hρ
    have hw1 := singularWeight_le_one ρ x
    have hsup := P.abs_mul_apply_le_weighted_sup hw0 hw1 hC₁ hC₂
      (hf₁.abs_apply_le_weight M hC₁ (hf₁T x hx hρ) hx hρ hw0 le_rfl)
      (fun i hi => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
        (hf₁V x hx hρ) hi)
      (hf₂.abs_apply_le_weight M hC₂ (hf₂T x hx hρ) hx hρ hw0 le_rfl)
      (fun j hj => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
        (hf₂W x hx hρ) hj) hη₁ hη₂ hη₁₂ (k := k)
    refine (abs_lowerProj_apply_le _ _).trans (hsup.trans ?_)
    have hG : 1 ≤ (1 + CΓ) ^ 2 := one_le_pow₀ (by linarith)
    have hp : 0 ≤ singularWeight ρ x ^ min (η - 𝒯.deg k) 0 := Real.rpow_nonneg hw0.le _
    calc P.const * (C₁ * C₂ * singularWeight ρ x ^ min (η - 𝒯.deg k) 0)
        ≤ P.truncMulConst * (C₁ * C₂ * singularWeight ρ x ^ min (η - 𝒯.deg k) 0) :=
          mul_le_mul_of_nonneg_right P.const_le_truncMulConst
            (mul_nonneg (mul_nonneg hC₁ hC₂) hp)
      _ = P.truncMulConst * C₁ * C₂ * 1 * singularWeight ρ x ^ min (η - 𝒯.deg k) 0 := by
          ring
      _ ≤ P.truncMulConst * C₁ * C₂ * (1 + CΓ) ^ 2 *
          singularWeight ρ x ^ min (η - 𝒯.deg k) 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG
            (mul_nonneg (mul_nonneg P.truncMulConst_nonneg hC₁) hC₂)) hp
  · exact M.abs_truncMul_increment_le_singular_near P hV hW hVα hWα hγ₁ hγ₂ hη₁ hη₂ hη₁₂ hηγ hreg
      hf₁V hf₂W hf₁T hf₂T hf₁ hf₂ hC₁ hC₂ hΓ₁ hΓ₂ hCΓ hx hy hρx hρy hd hk

end Model

end RegularityStructures

end
