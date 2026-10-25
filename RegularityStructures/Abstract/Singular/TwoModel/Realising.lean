/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.IntegrationData
public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.Model

/-!
# The difference model realises the kernel for `I⊕`

`isRealisingP_modelSum`: if `M₁, M₂` realise the kernel with profile `h` for `I` on `V`
(`Model.IsRealisingP`), then `M⊕` realises it for `I⊕` on `V⊕`, with the polynomial sector `P⊕`.
The left block is `Π⊕_x I⊕ e_{inl i} = λ⁻¹ (Π¹_x - Π²_x) (I e_i)`, matching the germ
`λ⁻¹ (g¹ - g²)` (`realGermP_modelSum_inl`) and the linearity of `Q_t` on germs of polynomial growth.
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

theorem regPi_modelSum_pairVec (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) (a : NonPoly P → ℝ) (b : ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).regPi x (pairVec P a b) t z =
      lam⁻¹ * (M₁.regPi x (extendNP P a) t z - M₂.regPi x (extendNP P a) t z) +
        M₂.regPi x b t z := by
  rw [regPi_modelSum, piSum_pairVec]
  simp [Model.regPi]

theorem intSum_pairVec (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : NonPoly P → ℝ) (b : ι → ℝ) :
    intSum P I (pairVec P a b) = pairVec P (restrictNP P (I (extendNP P a))) (I b) := by
  funext s
  rcases s with i | j
  · rfl
  · change (0 : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) a j + I b j = I b j
    simp

theorem regPi_modelSum_intSum_inl (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) (j : NonPoly P) (t : ℝ) (z : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).regPi x (intSum P I (Pi.single (Sum.inl j) 1)) t z =
      lam⁻¹ * (M₁.regPi x (I (Pi.single j.1 1)) t z - M₂.regPi x (I (Pi.single j.1 1)) t z) := by
  have e1 : M₁.regPi x (extendNP P (restrictNP P (I (Pi.single j.1 1)))) t z -
      M₂.regPi x (extendNP P (restrictNP P (I (Pi.single j.1 1)))) t z =
      M₁.regPi x (I (Pi.single j.1 1)) t z - M₂.regPi x (I (Pi.single j.1 1)) t z := by
    have := congrArg (fun F : parabolicSemigroup.distributions => (F : ℝ → ParabolicSpace → ℝ) t z)
      (pi_sub_extendNP_restrictNP h₁ h₂ x (I (Pi.single j.1 1)))
    simpa [Model.regPi] using this
  rw [single_inl, intSum_pairVec, extendNP_single, regPi_modelSum_pairVec, e1]
  simp [Model.regPi]

theorem regPi_modelSum_intSum_inr (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) (j : ι) (t : ℝ) (z : ParabolicSpace) :
    (modelSum (lam := lam) h₁ h₂).regPi x (intSum P I (Pi.single (Sum.inr j) 1)) t z =
      M₂.regPi x (I (Pi.single j 1)) t z := by
  rw [single_inr, intSum_pairVec, regPi_modelSum_pairVec]
  simp [Model.regPi]

theorem apply_const_mul_sub {g₁ g₂ : ParabolicSpace → ℝ} (hg₁ : PolyBounded g₁)
    (hg₂ : PolyBounded g₂) (c : ℝ) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    parabolicSemigroup.apply t (fun w => c * (g₁ w - g₂ w)) z =
      c * (parabolicSemigroup.apply t g₁ z - parabolicSemigroup.apply t g₂ z) := by
  rw [← hg₁.apply_sub hg₂ ht z]
  simp only [RegularisingSemigroup.apply, ← integral_const_mul]
  congr 1
  funext w
  ring

end TwoModel

end RegularityStructures

end
