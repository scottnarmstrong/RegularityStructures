/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModelsNear
public import RegularityStructures.Abstract.WeightedSingularTwoModelsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Truncation `Q_{<γ}` for the two-model singular bound, near-pair `Γ`-bounds

`SingularDiffBoundOn.lowerProj_near`: for `γ ≤ γ'`,
`|||Q_{<γ} f₁; Q_{<γ} f₂|||_{γ, η' ∧ γ; S} ≤ C_d (1 + |ι| C_Γ) + C₁ |ι| δ_Γ`, where `C_d` bounds
`|||f₁; f₂|||_{γ',η'}`, `C₁` bounds `|||f₁|||_{γ',η'}`, `C_Γ` bounds `Γ²` and `δ_Γ` bounds
`Γ¹ − Γ²`, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.

The extra term comes from `Γ¹ r₁ − Γ² r₂ = (Γ¹ − Γ²) r₁ + Γ² (r₁ − r₂)` with
`r_k = f_k − Q_{<γ} f_k`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- **Truncation on pairs in `D^{γ',η'}_P`**: for `γ ≤ γ'`,
`|||Q_{<γ} f₁; Q_{<γ} f₂|||_{γ, η' ∧ γ; S} ≤ C_d (1 + |ι| C_Γ) + C₁ |ι| δ_Γ`. -/
theorem SingularDiffBoundOn.lowerProj_near {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ}
    {γ γ' η' Cd C₁ CΓ δΓ : ℝ} {S : Set E} {f₁ f₂ : E → ι → ℝ}
    (hd : M₁.SingularDiffBoundOn M₂ ρ γ' η' Cd S f₁ f₂)
    (hf₁ : M₁.SingularBoundOn ρ γ' η' C₁ S f₁)
    (hf₁T : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ lowerSubspace 𝒯.deg γ')
    (hf₂T : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ lowerSubspace 𝒯.deg γ') (hγ : γ ≤ γ')
    (hΓ₂ : M₂.GammaNearOn γ' CΓ S) (hΓd : M₁.GammaDiffNearOn M₂ γ' δΓ S)
    (hCd : 0 ≤ Cd) (hC₁ : 0 ≤ C₁) (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) :
    M₁.SingularDiffBoundOn M₂ ρ γ (min η' γ)
      (Cd * (1 + Fintype.card ι * CΓ) + C₁ * Fintype.card ι * δΓ) S
      (fun x => RegularityStructures.lowerProj 𝒯.deg γ (f₁ x))
      (fun x => RegularityStructures.lowerProj 𝒯.deg γ (f₂ x)) := by
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hCd1 : Cd ≤ Cd * (1 + Fintype.card ι * CΓ) + C₁ * Fintype.card ι * δΓ := by
    nlinarith [mul_nonneg hN hCΓ, mul_nonneg hC₁ (mul_nonneg hN hδΓ), mul_nonneg hCd
      (mul_nonneg hN hCΓ)]
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hdist j hj => ?_⟩
  · have hw0 := singularWeight_pos hρ
    show |RegularityStructures.lowerProj 𝒯.deg γ (f₁ x) i -
      RegularityStructures.lowerProj 𝒯.deg γ (f₂ x) i| ≤ _
    rw [lowerProj_apply_of_lt hi, lowerProj_apply_of_lt hi]
    refine (hd.1 x hx hρ i (hi.trans_le hγ)).trans (mul_le_mul hCd1 ?_
      (Real.rpow_nonneg hw0.le _) (by positivity))
    exact Real.rpow_le_rpow_of_exponent_ge hw0 (singularWeight_le_one ρ x)
      (min_le_min (by linarith [min_le_left η' γ]) le_rfl)
  · set w := min (singularWeight ρ x) (singularWeight ρ y) with hw_def
    set d := K.scaleDist y x with hd_def
    have hw0 : 0 < w := lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have hw1 : w ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one ρ x)
    have hd0 : 0 ≤ d := K.scaleDist_nonneg y x
    have hj' : 𝒯.deg j < γ' := hj.trans_le hγ
    set X : ℝ := d ^ (γ - 𝒯.deg j) * w ^ (min η' γ - γ) with hX
    have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)
    set r₁ : ι → ℝ := f₁ x - RegularityStructures.lowerProj 𝒯.deg γ (f₁ x) with hr₁
    set r₂ : ι → ℝ := f₂ x - RegularityStructures.lowerProj 𝒯.deg γ (f₂ x) with hr₂
    have hdec : (RegularityStructures.lowerProj 𝒯.deg γ (f₁ y) -
        M₁.gammaMap y x (RegularityStructures.lowerProj 𝒯.deg γ (f₁ x))) j -
        (RegularityStructures.lowerProj 𝒯.deg γ (f₂ y) -
        M₂.gammaMap y x (RegularityStructures.lowerProj 𝒯.deg γ (f₂ x))) j =
        ((f₁ y - M₁.gammaMap y x (f₁ x)) j - (f₂ y - M₂.gammaMap y x (f₂ x)) j) +
          (M₁.gammaMap y x r₁ j - M₂.gammaMap y x r₂ j) := by
      simp only [hr₁, hr₂, map_sub, Pi.sub_apply, lowerProj_apply_of_lt hj]
      ring
    have h1 : |(f₁ y - M₁.gammaMap y x (f₁ x)) j - (f₂ y - M₂.gammaMap y x (f₂ x)) j| ≤
        Cd * X := by
      refine (hd.2 x hx y hy hρx hρy hdist j hj').trans ?_
      rw [mul_assoc, hX]
      exact mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_rpow_mul_rpow hd0 hdist hw0 hw1
        (by linarith) (by linarith) (by linarith [min_le_left η' γ])) hCd
    have hmain : ∀ i, γ ≤ 𝒯.deg i → 𝒯.deg i < γ' →
        d ^ (𝒯.deg i - 𝒯.deg j) * w ^ min (η' - 𝒯.deg i) 0 ≤ X := by
      intro i hiγ hiγ'
      refine rpow_mul_rpow_le_rpow_mul_rpow hd0 hdist hw0 hw1 (by linarith) (by linarith) ?_
      rcases min_cases (η' - 𝒯.deg i) 0 with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
        linarith [min_le_left η' γ, min_le_right η' γ]
    have hterm : ∀ i, |r₁ i * (M₁.gammaMap y x (Pi.single i 1) j -
        M₂.gammaMap y x (Pi.single i 1) j) + (r₁ i - r₂ i) * M₂.gammaMap y x (Pi.single i 1) j|
        ≤ C₁ * δΓ * X + Cd * CΓ * X := by
      intro i
      by_cases hiγ : 𝒯.deg i < γ
      · have e1 : r₁ i = 0 := by
          rw [hr₁, Pi.sub_apply, lowerProj_apply_of_lt hiγ, sub_self]
        have e2 : r₂ i = 0 := by
          rw [hr₂, Pi.sub_apply, lowerProj_apply_of_lt hiγ, sub_self]
        rw [e1, e2]
        simp only [zero_mul, sub_zero, add_zero, abs_zero]
        positivity
      by_cases hiγ' : 𝒯.deg i < γ'
      · have hri₁ : r₁ i = f₁ x i := by
          rw [hr₁, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ), sub_zero]
        have hri₂ : r₂ i = f₂ x i := by
          rw [hr₂, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ), sub_zero]
        have hji : 𝒯.deg j < 𝒯.deg i := hj.trans_le (not_lt.1 hiγ)
        have hfx := hf₁.abs_apply_le_weight M₁ hC₁ (hf₁T x hx hρx) hx hρx hw0 (min_le_left _ _) i
        have hdx := hd.abs_sub_apply_le_weight hCd (hf₁T x hx hρx) (hf₂T x hx hρx) hx hρx hw0
          (min_le_left _ _) i
        have hΓ2 : |M₂.gammaMap y x (Pi.single i 1) j| ≤ CΓ * d ^ (𝒯.deg i - 𝒯.deg j) :=
          hΓ₂ i j hiγ' hji x hx y hy (le_gammaNearRadius_of_le_one (hdist.trans hw1))
        have hΓ1 : |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| ≤
            δΓ * d ^ (𝒯.deg i - 𝒯.deg j) := hΓd i j hiγ' hji x hx y hy (le_gammaNearRadius_of_le_one (hdist.trans hw1))
        have hm := hmain i (not_lt.1 hiγ) hiγ'
        have hp0 : 0 ≤ d ^ (𝒯.deg i - 𝒯.deg j) := Real.rpow_nonneg hd0 _
        have hq0 : 0 ≤ w ^ min (η' - 𝒯.deg i) 0 := Real.rpow_nonneg hw0.le _
        rw [hri₁, hri₂]
        have ha : |f₁ x i * (M₁.gammaMap y x (Pi.single i 1) j -
            M₂.gammaMap y x (Pi.single i 1) j)| ≤ C₁ * δΓ * X := by
          rw [abs_mul]
          calc _ ≤ (C₁ * w ^ min (η' - 𝒯.deg i) 0) * (δΓ * d ^ (𝒯.deg i - 𝒯.deg j)) :=
                mul_le_mul hfx hΓ1 (abs_nonneg _) (by positivity)
            _ = C₁ * δΓ * (d ^ (𝒯.deg i - 𝒯.deg j) * w ^ min (η' - 𝒯.deg i) 0) := by ring
            _ ≤ C₁ * δΓ * X := mul_le_mul_of_nonneg_left hm (mul_nonneg hC₁ hδΓ)
        have hb : |(f₁ x i - f₂ x i) * M₂.gammaMap y x (Pi.single i 1) j| ≤ Cd * CΓ * X := by
          rw [abs_mul]
          calc _ ≤ (Cd * w ^ min (η' - 𝒯.deg i) 0) * (CΓ * d ^ (𝒯.deg i - 𝒯.deg j)) :=
                mul_le_mul hdx hΓ2 (abs_nonneg _) (by positivity)
            _ = Cd * CΓ * (d ^ (𝒯.deg i - 𝒯.deg j) * w ^ min (η' - 𝒯.deg i) 0) := by ring
            _ ≤ Cd * CΓ * X := mul_le_mul_of_nonneg_left hm (mul_nonneg hCd hCΓ)
        exact (abs_add_le _ _).trans (add_le_add ha hb)
      · have e1 : r₁ i = 0 := by
          rw [hr₁, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ),
            hf₁T x hx hρx i (not_lt.1 hiγ'), sub_zero]
        have e2 : r₂ i = 0 := by
          rw [hr₂, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ),
            hf₂T x hx hρx i (not_lt.1 hiγ'), sub_zero]
        rw [e1, e2]
        simp only [zero_mul, sub_zero, add_zero, abs_zero]
        positivity
    have h2 : |M₁.gammaMap y x r₁ j - M₂.gammaMap y x r₂ j| ≤
        Fintype.card ι * (C₁ * δΓ * X + Cd * CΓ * X) := by
      rw [M₁.gammaMap_apply_eq_sum x y r₁ j, M₂.gammaMap_apply_eq_sum x y r₂ j,
        ← Finset.sum_sub_distrib]
      have e : ∀ i, r₁ i * M₁.gammaMap y x (Pi.single i 1) j -
          r₂ i * M₂.gammaMap y x (Pi.single i 1) j =
          r₁ i * (M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j) +
            (r₁ i - r₂ i) * M₂.gammaMap y x (Pi.single i 1) j := fun i => by ring
      simp_rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact le_rfl
    rw [hdec]
    calc _ ≤ Cd * X + Fintype.card ι * (C₁ * δΓ * X + Cd * CΓ * X) :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = _ := by
        rw [hX]
        ring

end Model

end RegularityStructures

end
