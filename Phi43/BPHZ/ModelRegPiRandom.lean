/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTree
public import Phi43.BPHZ.CanonicalBridgeHairer
public import Phi43.BPHZ.TreeI3Psi2TestedMoment
public import Phi43.BPHZ.TreeI2Psi2TestedMoment
public import Phi43.BPHZ.TreeI3PsiField
public import RegularityStructures.Abstract.Model

/-!
# The random models realise the named tree fields, almost surely

Let `ξ ε` be a regularised noise and `Z : Ω → Model` with
`IsPhi43ModelOf N κ (ξ ω) (c_ε, C₂) (Z ω)` for almost every `ω`, where
`(c_ε, C₂) = (hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε)`.  Then for each
`τ ∈ F₋ ∖ {Ψ²Xᵢ}` and `t > 0`, almost surely
`(Z ω).regPi x (Pi.single τ 1) t x = ∫ q^♯_t(x, u) F_τ(ω, u) du`
with `F_τ` the named field of the tree (`regularisedNoise`, `hairerPsiField`,
`hairerPsiWickSquare`, `hairerPsiWickCube`, `hairerI3PsiField`, `hairerI2Psi2Field`,
`hairerI3Psi2Field`, with base point `spaceTimeProj x`).

The ambient hypothesis on integrability of `Q_t(x, ·) F_τ(ω, proj ·)` over `ℝ⁴` is stated for
almost every `ω`; for `Ψ` it is proved in `ModelRegPiPsi`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- Slices of a jointly measurable field are measurable. -/
theorem measurable_slice_of_uncurry {Ω : Type*} [MeasurableSpace Ω] {F : Ω → SpaceTime → ℝ}
    (h : Measurable (fun q : Ω × SpaceTime => F q.1 q.2)) (ω : Ω) : Measurable (F ω) := by
  have h' := h.comp (measurable_prodMk_left (x := ω))
  simpa only [Function.comp_def] using h'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {κ : Kappa}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- **Random corollary, generic form.**  If the tree field of `τ` at the Hairer constants is the
field `F`, then almost surely `regPi` is the integral of `F` against the periodised kernel. -/
theorem ae_regPi_single_eq_integral_semigroupPeriodised
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {τ : Symbol} (hτ : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) {F : Ω → SpaceTime → ℝ}
    (hF : ∀ ω, hairerTreeField N ξ (hairerWickConstant N ρ ε) (hairerSunsetConstant N ρ ε)
      (spaceTimeProj x) ω τ = F ω)
    (hFm : ∀ ω, Measurable (F ω))
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * F ω (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single τ 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * F ω u := by
  filter_upwards [hZ, hint] with ω hω hi
  have h := hω.regPi_single_eq_integral_semigroupPeriodised hτ hX ht x
    (by rw [show (C₁ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerWickConstant N ρ ε from rfl,
        show (C₂ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerSunsetConstant N ρ ε from rfl, hF ω]
        exact hFm ω)
    (by rw [show (C₁ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerWickConstant N ρ ε from rfl,
        show (C₂ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerSunsetConstant N ρ ε from rfl, hF ω]
        exact hi)
  rw [h]
  simp only [show (C₁ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerWickConstant N ρ ε from rfl,
        show (C₂ ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
        RenormalisationConstants)) = hairerSunsetConstant N ρ ε from rfl, hF ω]

/-- Random corollary for `Ξ`. -/
theorem ae_regPi_single_noise_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (ξ ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .noise 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (ξ ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => ξ ω) (fun _ => rfl) (fun ω => (IsSmoothOnSpaceTime.continuous (hξ.1 ω)).measurable) hint

/-- Random corollary for `Ψ`. -/
theorem ae_regPi_single_psi_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerPsiField N ξ ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .psi 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerPsiField N ξ ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerPsiField N ξ ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerPsiField_uncurry N hξ) ω) hint

/-- Random corollary for `Ψ²`. -/
theorem ae_regPi_single_psiSq_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerPsiWickSquare N ρ ε ξ ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .psiSq 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerPsiWickSquare N ρ ε ξ ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerPsiWickSquare N ρ ε ξ ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerPsiWickSquare_uncurry N hξ) ω) hint

/-- Random corollary for `Ψ³`. -/
theorem ae_regPi_single_psiCube_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerPsiWickCube N ρ ε ξ ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .psiCube 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerPsiWickCube N ρ ε ξ ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerPsiWickCube N ρ ε ξ ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerPsiWickCube_uncurry N hξ) ω) hint

/-- Random corollary for `I(Ψ³)Ψ`. -/
theorem ae_regPi_single_iPsiCubePsi_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .iPsiCubePsi 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerI3PsiField_uncurry N hξ (spaceTimeProj x)) ω) hint

/-- Random corollary for `I(Ψ²)Ψ²`. -/
theorem ae_regPi_single_iPsiSqPsiSq_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .iPsiSqPsiSq 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerI2Psi2Field_uncurry N hξ (spaceTimeProj x)) ω) hint

/-- Random corollary for `I(Ψ³)Ψ²`. -/
theorem ae_regPi_single_iPsiCubePsiSq_eq
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Z ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * (hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω) (spaceTimeProj y))) :
    (fun ω => (Z ω).regPi x (Pi.single .iPsiCubePsiSq 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * (hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω) u :=
  ae_regPi_single_eq_integral_semigroupPeriodised hZ
    (by simp [mem_fMinus_iff_isFMinus, isFMinus]) (fun _ h => Symbol.noConfusion h) ht x
    (F := fun ω => hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω) (fun _ => rfl) (fun ω => measurable_slice_of_uncurry (measurable_hairerI3Psi2Field_uncurry N hξ (spaceTimeProj x)) ω) hint

end RegularityStructures.Phi43

end
