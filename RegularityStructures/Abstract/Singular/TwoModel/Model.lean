/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Struct
public import RegularityStructures.Abstract.Model

/-!
# The difference model `M⊕`

`Π⊕_x (a, b) = λ⁻¹ (Π¹_x - Π²_x) E₀ a + Π²_x b` (`piSum`), and `modelSum`, the model
`M⊕ : Model 𝒯⊕ parabolicSemigroup` with `Γ⊕_{xy}` (`pi_gamma` by `piSum_gammaSum`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') (lam : ℝ) (M₁ M₂ : Model 𝒯 parabolicSemigroup)

/-- `Π⊕_x (a, b) = λ⁻¹ (Π¹_x - Π²_x) E₀ a + Π²_x b`. -/
def piSum (x : ParabolicSpace) :
    (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] parabolicSemigroup.distributions :=
  lam⁻¹ • ((M₁.pi x - M₂.pi x) ∘ₗ extendNP P ∘ₗ leftPart P) + M₂.pi x ∘ₗ rightPart P

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem piSum_apply (x : ParabolicSpace) (v : NonPoly P ⊕ ι → ℝ) :
    piSum P lam M₁ M₂ x v =
      lam⁻¹ • (M₁.pi x (extendNP P (leftPart P v)) - M₂.pi x (extendNP P (leftPart P v))) +
        M₂.pi x (rightPart P v) := rfl

theorem piSum_pairVec (x : ParabolicSpace) (a : NonPoly P → ℝ) (b : ι → ℝ) :
    piSum P lam M₁ M₂ x (pairVec P a b) =
      lam⁻¹ • (M₁.pi x (extendNP P a) - M₂.pi x (extendNP P a)) + M₂.pi x b := rfl

theorem piSum_gammaSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y : ParabolicSpace) (v : NonPoly P ⊕ ι → ℝ) :
    piSum P lam M₁ M₂ x (gammaSum P lam M₁ M₂ x y v) = piSum P lam M₁ M₂ y v := by
  have key := pi_sub_extendNP_restrictNP h₁ h₂ x (M₁.gammaMap x y (extendNP P (leftPart P v)))
  simp only [piSum_apply, gammaSum, leftPart_blockMap, rightPart_blockMap, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, key, map_add, map_smul,
    map_sub, Model.pi_gammaMap]
  module

theorem coe_piSum_single_inl (x : ParabolicSpace) (j : NonPoly P) (t : ℝ) (z : ParabolicSpace) :
    (piSum P lam M₁ M₂ x (Pi.single (Sum.inl j) 1) : ℝ → ParabolicSpace → ℝ) t z =
      lam⁻¹ * (M₁.regPi x (Pi.single j.1 1) t z - M₂.regPi x (Pi.single j.1 1) t z) := by
  rw [single_inl, piSum_pairVec, extendNP_single]
  simp [Model.regPi]

theorem coe_piSum_single_inr (x : ParabolicSpace) (j : ι) (t : ℝ) (z : ParabolicSpace) :
    (piSum P lam M₁ M₂ x (Pi.single (Sum.inr j) 1) : ℝ → ParabolicSpace → ℝ) t z =
      M₂.regPi x (Pi.single j 1) t z := by
  rw [single_inr, piSum_pairVec]
  simp [Model.regPi]

theorem measurable_diag_piSum (hd₁ : ∀ i ⦃t : ℝ⦄, 0 < t →
      Measurable fun x => (M₁.pi x (Pi.single i 1) : ℝ → ParabolicSpace → ℝ) t x)
    (hd₂ : ∀ i ⦃t : ℝ⦄, 0 < t →
      Measurable fun x => (M₂.pi x (Pi.single i 1) : ℝ → ParabolicSpace → ℝ) t x)
    (s : NonPoly P ⊕ ι) {t : ℝ} (ht : 0 < t) :
    Measurable fun x => (piSum P lam M₁ M₂ x (Pi.single s 1) : ℝ → ParabolicSpace → ℝ) t x := by
  rcases s with j | j
  · simp only [coe_piSum_single_inl]
    exact ((hd₁ j.1 ht).sub (hd₂ j.1 ht)).const_mul _
  · simp only [coe_piSum_single_inr]
    exact hd₂ j ht

theorem measurable_piSum (hm₁ : ∀ x i ⦃t : ℝ⦄, 0 < t →
      Measurable ((M₁.pi x (Pi.single i 1) : ℝ → ParabolicSpace → ℝ) t))
    (hm₂ : ∀ x i ⦃t : ℝ⦄, 0 < t →
      Measurable ((M₂.pi x (Pi.single i 1) : ℝ → ParabolicSpace → ℝ) t))
    (x : ParabolicSpace) (s : NonPoly P ⊕ ι) {t : ℝ} (ht : 0 < t) :
    Measurable ((piSum P lam M₁ M₂ x (Pi.single s 1) : ℝ → ParabolicSpace → ℝ) t) := by
  rcases s with j | j
  · have : (piSum P lam M₁ M₂ x (Pi.single (Sum.inl j) 1) : ℝ → ParabolicSpace → ℝ) t =
        fun z => lam⁻¹ * (M₁.regPi x (Pi.single j.1 1) t z - M₂.regPi x (Pi.single j.1 1) t z) :=
      funext fun z => coe_piSum_single_inl x j t z
    rw [this]
    exact ((hm₁ x j.1 ht).sub (hm₂ x j.1 ht)).const_mul _
  · have : (piSum P lam M₁ M₂ x (Pi.single (Sum.inr j) 1) : ℝ → ParabolicSpace → ℝ) t =
        fun z => M₂.regPi x (Pi.single j 1) t z :=
      funext fun z => coe_piSum_single_inr x j t z
    rw [this]
    exact hm₂ x j ht

/-- The difference model `M⊕ : Model 𝒯⊕ parabolicSemigroup` built from `M₁` and `M₂`, whose
modelled distributions encode pairs and their differences ([Hai14, Theorem 7.1], two-model half). -/
@[expose] noncomputable def modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) :
    Model (structSumU P) parabolicSemigroup where
  pi := piSum P lam M₁ M₂
  gamma x y := ⟨gammaUnit P lam M₁ M₂ h₁ h₂ x y, gammaUnit_mem_groupSumU h₁ h₂ x y⟩
  pi_gamma x y τ := piSum_gammaSum h₁ h₂ x y τ
  gamma_self x := Subtype.ext (gammaUnit_self h₁ h₂ x)
  gamma_mul x y z := Subtype.ext (gammaUnit_mul h₁ h₂ x y z)
  measurable_diag i _ ht := measurable_diag_piSum M₁.measurable_diag M₂.measurable_diag i ht
  measurable_pi x i _ ht := measurable_piSum M₁.measurable_pi M₂.measurable_pi x i ht

theorem gammaMap_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).gammaMap x y = gammaSum P lam M₁ M₂ x y := rfl

theorem regPi_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) (v : NonPoly P ⊕ ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).regPi x v t z = (piSum P lam M₁ M₂ x v : ℝ → _ → ℝ) t z := rfl

end TwoModel

end RegularityStructures

end
