/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.BoundsG
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Common qualitative growth of two models and of the difference model

Qualitative statements (no constants are used downstream) for the window chain of the two-model
Theorem 7.1: if each of two models `M₁, M₂` has *some* growth model (`Model.GrowthModel`, with its
own weights and exponents), then

* `TwoModel.exists_common_growthModel`: both have a growth model with the *same* weights
  `ρP, ρG` and exponents `p, qG`;
* `TwoModel.exists_growthModel_modelSum`: the difference model `M⊕ = modelSum h₁ h₂` has a growth
  model (the weighted difference bounds follow from the triangle inequality).
-/

public section

open Set

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ : ℝ}

/-- The sum of two moderate weights is moderate for any common larger exponent. -/
theorem isModerateWeight_add {ρ₁ ρ₂ : ParabolicSpace → ℝ} {p₁ p₂ p : ℝ}
    (h₁ : parabolicSemigroup.IsModerateWeight ρ₁ p₁)
    (h₂ : parabolicSemigroup.IsModerateWeight ρ₂ p₂) (hp₁ : p₁ ≤ p) (hp₂ : p₂ ≤ p) :
    parabolicSemigroup.IsModerateWeight (fun x => ρ₁ x + ρ₂ x) p where
  one_le x := by
    have := h₁.one_le x
    have := h₂.one_le x
    linarith
  measurable := h₁.measurable.add h₂.measurable
  nonneg_exp := h₁.nonneg_exp.trans hp₁
  le y z := by
    have hb : 1 ≤ 1 + parabolicSemigroup.scaleDist z y := by
      linarith [parabolicSemigroup.scaleDist_nonneg z y]
    have e₁ : (1 + parabolicSemigroup.scaleDist z y) ^ p₁ ≤
        (1 + parabolicSemigroup.scaleDist z y) ^ p :=
      Real.rpow_le_rpow_of_exponent_le hb hp₁
    have e₂ : (1 + parabolicSemigroup.scaleDist z y) ^ p₂ ≤
        (1 + parabolicSemigroup.scaleDist z y) ^ p :=
      Real.rpow_le_rpow_of_exponent_le hb hp₂
    have a₁ := h₁.le y z
    have a₂ := h₂.le y z
    have n₁ : 0 ≤ ρ₁ y := by linarith [h₁.one_le y]
    have n₂ : 0 ≤ ρ₂ y := by linarith [h₂.one_le y]
    show ρ₁ z + ρ₂ z ≤ (ρ₁ y + ρ₂ y) * _
    nlinarith [mul_le_mul_of_nonneg_left e₁ n₁, mul_le_mul_of_nonneg_left e₂ n₂]

private theorem piBoundGrowth_mono {M : Model 𝒯 parabolicSemigroup} {C : ℝ} {ρ ρ' : ParabolicSpace → ℝ}
    (h : M.PiBoundGrowth γ C ρ) (hC : 0 ≤ C) (hle : ∀ x, ρ x ≤ ρ' x) :
    M.PiBoundGrowth γ C ρ' := by
  intro i hi t ht x
  have hw : 0 ≤ t ^ (𝒯.deg i / parabolicSemigroup.order) := Real.rpow_nonneg ht.1.le _
  refine (h i hi t ht x).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle x) hC) hw

private theorem gammaBoundGrowth_mono {M : Model 𝒯 parabolicSemigroup} {C : ℝ}
    {ρ ρ' : ParabolicSpace → ℝ} {q q' : ℝ} (h : M.GammaBoundGrowth γ C ρ q)
    (hρ : ∀ x, 0 ≤ ρ x) (hle : ∀ x, ρ x ≤ ρ' x) (hq : q ≤ q') :
    M.GammaBoundGrowth γ (max C 0) ρ' q' := by
  intro i j hi hj x y
  have hd := parabolicSemigroup.scaleDist_nonneg y x
  have hu : 0 ≤ (1 + parabolicSemigroup.scaleDist y x) ^ q :=
    Real.rpow_nonneg (by linarith) _
  have hv : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
    Real.rpow_nonneg hd _
  have huu : (1 + parabolicSemigroup.scaleDist y x) ^ q ≤
      (1 + parabolicSemigroup.scaleDist y x) ^ q' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hq
  refine (h i j hi hj x y).trans ?_
  set u := (1 + parabolicSemigroup.scaleDist y x) ^ q
  set u' := (1 + parabolicSemigroup.scaleDist y x) ^ q'
  set v := parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
  have h0 : 0 ≤ ρ x * u * v := mul_nonneg (mul_nonneg (hρ x) hu) hv
  have h1 : C * ρ x * u * v ≤ max C 0 * ρ x * u * v := by
    have := mul_le_mul_of_nonneg_right (le_max_left C 0) h0
    calc C * ρ x * u * v = C * (ρ x * u * v) := by ring
      _ ≤ max C 0 * (ρ x * u * v) := this
      _ = _ := by ring
  refine h1.trans ?_
  have hm : 0 ≤ max C 0 := le_max_right _ _
  have h2 : ρ x * u ≤ ρ' x * u' := mul_le_mul (hle x) huu hu ((hρ x).trans (hle x))
  calc max C 0 * ρ x * u * v = max C 0 * (ρ x * u) * v := by ring
    _ ≤ max C 0 * (ρ' x * u') * v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hm) hv
    _ = _ := by ring

/-- Two growth models for the same level `γ` have a common growth model (common weights and
exponents). -/
theorem exists_common_growthModel
    (g₁ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel γ C' C'' ρP ρG p q)
    (g₂ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel γ C' C'' ρP ρG p q) :
    ∃ (C₁ C₁' C₂ C₂' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel γ C₁ C₁' ρP ρG p q ∧ M₂.GrowthModel γ C₂ C₂' ρP ρG p q := by
  obtain ⟨a₁, b₁, ρP₁, ρG₁, p₁, q₁, G₁⟩ := g₁
  obtain ⟨a₂, b₂, ρP₂, ρG₂, p₂, q₂, G₂⟩ := g₂
  have mP := isModerateWeight_add G₁.moderateP G₂.moderateP (le_max_left p₁ p₂)
    (le_max_right p₁ p₂)
  have mG := isModerateWeight_add G₁.moderateG G₂.moderateG (le_max_left p₁ p₂)
    (le_max_right p₁ p₂)
  have pP₁ : ∀ x, 0 ≤ ρP₁ x := fun x => by linarith [G₁.moderateP.one_le x]
  have pP₂ : ∀ x, 0 ≤ ρP₂ x := fun x => by linarith [G₂.moderateP.one_le x]
  have pG₁ : ∀ x, 0 ≤ ρG₁ x := fun x => by linarith [G₁.moderateG.one_le x]
  have pG₂ : ∀ x, 0 ≤ ρG₂ x := fun x => by linarith [G₂.moderateG.one_le x]
  refine ⟨a₁, max b₁ 0, a₂, max b₂ 0, fun x => ρP₁ x + ρP₂ x, fun x => ρG₁ x + ρG₂ x,
    max p₁ p₂, max q₁ q₂, ⟨G₁.pos, mP, mG, G₁.nonnegG.trans (le_max_left _ _),
      piBoundGrowth_mono G₁.piBound G₁.piBound_nonneg fun x => by linarith [pP₂ x],
      gammaBoundGrowth_mono G₁.gammaBound pG₁ (fun x => by linarith [pG₂ x]) (le_max_left _ _),
      G₁.piBound_nonneg⟩,
    ⟨G₂.pos, mP, mG, G₂.nonnegG.trans (le_max_right _ _),
      piBoundGrowth_mono G₂.piBound G₂.piBound_nonneg fun x => by linarith [pP₁ x],
      gammaBoundGrowth_mono G₂.gammaBound pG₂ (fun x => by linarith [pG₁ x]) (le_max_right _ _),
      G₂.piBound_nonneg⟩⟩

/-- **The difference model has a growth model**, qualitatively: from growth models of `M₁` and `M₂`
(arbitrary constants, weights and exponents). -/
theorem exists_growthModel_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam)
    (g₁ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel γ C' C'' ρP ρG p q)
    (g₂ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel γ C' C'' ρP ρG p q) :
    ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      (modelSum (lam := lam) h₁ h₂).GrowthModel γ C' C'' ρP ρG p q := by
  obtain ⟨a₁, b₁, a₂, b₂, ρP, ρG, p, q, G₁, G₂⟩ := exists_common_growthModel g₁ g₂
  have hdP : M₁.PiDiffBoundGrowth M₂ γ (a₁ + a₂) ρP := by
    intro i hi t ht x
    have e₁ := G₁.piBound i hi t ht x
    have e₂ := G₂.piBound i hi t ht x
    refine (abs_sub _ _).trans ?_
    linarith
  have hdG : M₁.GammaDiffBoundGrowth M₂ γ (b₁ + b₂) ρG q := by
    intro i j hi hj x y
    have e₁ := G₁.gammaBound i j hi hj x y
    have e₂ := G₂.gammaBound i j hi hj x y
    refine (abs_sub _ _).trans ?_
    linarith
  exact ⟨_, _, ρP, ρG, p, q, growthModel_modelSum h₁ h₂ hlam G₁ G₂ hdP hdG⟩

end TwoModel

end RegularityStructures

end
