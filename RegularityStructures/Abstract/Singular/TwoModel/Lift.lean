/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.Model

/-!
# Lifting a pair of modelled functions to the difference model

`liftVec P λ u v = (λ • Q u, u - v)` and, for functions, `x ↦ liftVec P λ (f₁ x) (f₂ x)`
(the lift `f⊕` of a pair of modelled distributions). For polynomial-compatible `M₁, M₂` and `λ ≠ 0`:

* `piSum_liftVec`: `Π⊕_x (f⊕ x) = Π¹_x (f₁ x) - Π²_x (f₂ x)`;
* `liftVec_sub_gammaSum`: the increment identity
  `f⊕ y - Γ⊕_{yx} f⊕ x = (λ • Q (f₁ y - Γ¹_{yx} f₁ x), (f₁ y - Γ¹_{yx} f₁ x) - (f₂ y - Γ²_{yx} f₂ x))`;
* `singularBoundOn_liftSum`: `M₁.SingularBoundOn ρ γ η C₁ S f₁` and
  `M₁.SingularDiffBoundOn M₂ ρ γ η Cd S f₁ f₂` give
  `M⊕.SingularBoundOn ρ γ η (max (λ C₁) Cd) S f⊕`;
* `restrict_gammaSum_inr`, `gammaMap_sub_apply_eq`: the read-off lemma.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') (lam : ℝ)

/-- The lift `(λ • Q u, u - v)` of a pair of vectors `(u, v)` to `ι⊕ → ℝ`. -/
def liftVec (u v : ι → ℝ) : NonPoly P ⊕ ι → ℝ :=
  pairVec P (lam • restrictNP P u) (u - v)

/-- The lift `f⊕ x = (λ • Q (f₁ x), f₁ x - f₂ x)` of a pair of functions. -/
def liftSum {E : Type*} (f₁ f₂ : E → ι → ℝ) (x : E) : NonPoly P ⊕ ι → ℝ :=
  liftVec P lam (f₁ x) (f₂ x)

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem piSum_liftVec (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (x : ParabolicSpace) (u v : ι → ℝ) :
    piSum P lam M₁ M₂ x (liftVec P lam u v) = M₁.pi x u - M₂.pi x v := by
  have key := pi_sub_extendNP_restrictNP h₁ h₂ x u
  have key' : M₁.pi x (extendNP P (restrictNP P u)) =
      M₁.pi x u - M₂.pi x u + M₂.pi x (extendNP P (restrictNP P u)) := by
    rw [← key]; abel
  simp only [liftVec, piSum_pairVec, map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hlam,
    one_smul, map_sub]
  rw [key']
  abel

theorem piSum_liftSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) {f₁ f₂ : ParabolicSpace → ι → ℝ} (x : ParabolicSpace) :
    piSum P lam M₁ M₂ x (liftSum P lam f₁ f₂ x) = M₁.pi x (f₁ x) - M₂.pi x (f₂ x) :=
  piSum_liftVec h₁ h₂ hlam x _ _

theorem liftVec_sub_gammaSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (x y : ParabolicSpace) (u v u' v' : ι → ℝ) :
    liftVec P lam u' v' - gammaSum P lam M₁ M₂ y x (liftVec P lam u v) =
      pairVec P (lam • restrictNP P (u' - M₁.gammaMap y x u))
        ((u' - M₁.gammaMap y x u) - (v' - M₂.gammaMap y x v)) := by
  have key := gammaMap_sub_extendNP_restrictNP h₁ h₂ y x u
  have key' : M₁.gammaMap y x (extendNP P (restrictNP P u)) =
      M₁.gammaMap y x u - M₂.gammaMap y x u + M₂.gammaMap y x (extendNP P (restrictNP P u)) := by
    rw [← key]; abel
  have hQ := restrictNP_gammaMap_extendNP_restrictNP (P := P) M₁ y x u
  rw [liftVec, liftVec, gammaSum_pairVec, ← pairVec_sub]
  congr 1
  · simp only [map_smul, hQ, map_sub, smul_sub]
  · simp only [map_smul, map_sub, smul_sub, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [key']
    abel

theorem liftSum_sub_gammaSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) {f₁ f₂ : ParabolicSpace → ι → ℝ} (x y : ParabolicSpace) :
    liftSum P lam f₁ f₂ y - gammaSum P lam M₁ M₂ y x (liftSum P lam f₁ f₂ x) =
      pairVec P (lam • restrictNP P (f₁ y - M₁.gammaMap y x (f₁ x)))
        ((f₁ y - M₁.gammaMap y x (f₁ x)) - (f₂ y - M₂.gammaMap y x (f₂ x))) :=
  liftVec_sub_gammaSum h₁ h₂ hlam x y _ _ _ _

private theorem abs_mul_le_aux {lam C C' a b z : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : |z| ≤ C * a * b) (hC : lam * C ≤ C') : |lam * z| ≤ C' * a * b := by
  rw [abs_mul, abs_of_pos hlam]
  calc lam * |z| ≤ lam * (C * a * b) := mul_le_mul_of_nonneg_left h hlam.le
    _ = (lam * C) * a * b := by ring
    _ ≤ C' * a * b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ha) hb

private theorem abs_mul_le_aux' {lam C C' w z : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w)
    (h : |z| ≤ C * w) (hC : lam * C ≤ C') : |lam * z| ≤ C' * w := by
  have := abs_mul_le_aux (a := w) (b := 1) hlam hw zero_le_one (by simpa using h) hC
  simpa using this

/-- Transfer of the singular bounds to the difference model: from the bound of `f₁` for `M₁` and
the comparison `|||f₁; f₂|||` we get the bound of `f⊕` for `M⊕` with constant
`max (λ C₁) Cd`. -/
theorem singularBoundOn_liftSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {ρ : ParabolicSpace → ℝ} {γ η C₁ Cd : ℝ} {S : Set ParabolicSpace}
    {f₁ f₂ : ParabolicSpace → ι → ℝ} (hf : M₁.SingularBoundOn ρ γ η C₁ S f₁)
    (hfd : M₁.SingularDiffBoundOn M₂ ρ γ η Cd S f₁ f₂) :
    (modelSum (lam := lam) h₁ h₂).SingularBoundOn ρ γ η (max (lam * C₁) Cd) S
      (liftSum P lam f₁ f₂) := by
  refine ⟨fun x hx hρ s hs => ?_, fun x hx y hy hρx hρy hd s hs => ?_⟩
  · have hw : 0 ≤ singularWeight ρ x ^ min (η - (structSumU P).deg s) 0 :=
      Real.rpow_nonneg (singularWeight_pos hρ).le _
    rcases s with i | j
    · have hi : 𝒯.deg i.1 < γ := hs
      exact abs_mul_le_aux' hlam hw (hf.1 x hx hρ i.1 hi) (le_max_left _ _)
    · have hj : 𝒯.deg j < γ := hs
      exact (hfd.1 x hx hρ j hj).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)
  · have hmin : 0 < min (singularWeight ρ x) (singularWeight ρ y) :=
      lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have ha : 0 ≤ parabolicSemigroup.scaleDist y x ^
        (γ - (structSumU P).deg s) :=
      Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _
    have hb : 0 ≤ min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ) :=
      Real.rpow_nonneg hmin.le _
    rw [gammaMap_modelSum, liftSum_sub_gammaSum h₁ h₂ hlam.ne']
    rcases s with i | j
    · have hi : 𝒯.deg i.1 < γ := hs
      exact abs_mul_le_aux hlam ha hb (hf.2 x hx y hy hρx hρy hd i.1 hi) (le_max_left _ _)
    · have hj : 𝒯.deg j < γ := hs
      exact (hfd.2 x hx y hy hρx hρy hd j hj).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ha) hb)

end TwoModel

end RegularityStructures

end
