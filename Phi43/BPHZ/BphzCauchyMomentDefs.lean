/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.RandomCanonical
public import Phi43.BPHZ.GammaFullMinkowski
import Mathlib.Tactic

/-!
# The `Π`-moment statements of the Cauchy argument for the BPHZ models

Two families of propositions.

* The moment statements `PiMomentCanonical`, `PiMomentCanonicalSub`, `PiMomentModelSub` for one
  symbol `i`, universally quantified over the mollifiers and the exponents: exactly the shape of
  `regPi_iPsiSq_lintegral_enorm_pow_le`, `regPi_iPsiCube_sub_lintegral_enorm_pow_le` (canonical
  model of a lifted noise) and of `regPi_psi_sub_lintegral_enorm_pow_le` (arbitrary family of
  `IsPhi43ModelOf` models).  The Cauchy argument takes some of them as hypotheses
  (`BphzCauchyMoments`, which holds by `bphzCauchyMoments_holds`).
* The uniform-in-the-noise single and difference bounds `PiSingleBound`, `PiSubBound` for the
  canonical models with Hairer's constants, monotone in the constant.
-/

@[expose] public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Single-model `Π`-moment of the canonical model of a lifted noise, for the symbol `i`. -/
def PiMomentCanonical (N : ℕ) (κ : Kappa) (i : Symbol) : Prop :=
  ∀ {ρ : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → ∀ {κbar : ℝ}, 0 ≤ κbar → κbar ≤ κ.1 / 2 →
    ∀ {q : ℕ}, 1 ≤ q →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ Cst = hairerWickConstant N ρ ε → (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
            parabolicSemigroup.order)) ^ q

/-- Difference `Π`-moment of two canonical models of lifted noises (two mollifiers), for the
symbol `i`. -/
def PiMomentCanonicalSub (N : ℕ) (κ : Kappa) (i : Symbol) : Prop :=
  ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
    0 ≤ κbar → 0 < θ → κbar + θ ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      C₁ Cst = hairerWickConstant N ρ ε → C₁ Cst' = hairerWickConstant N ρ' ε' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg i + κbar) /
              parabolicSemigroup.order)) ^ q

/-- Difference `Π`-moment of two families of `IsPhi43ModelOf` models, for the symbol `i`. -/
def PiMomentModelSub (N : ℕ) (κ : Kappa) (i : Symbol) : Prop :=
  ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
    0 ≤ κbar → 0 < θ → κbar + θ ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      (Z Z' : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ' ω)
        ((hairerWickConstant N ρ' ε', hairerSunsetConstant N ρ' ε') : RenormalisationConstants)
        (Z' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x - (Z' ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg i + κbar) /
              parabolicSemigroup.order)) ^ q

/-- The `Π`-moments (single and difference) of the symbols `iPsiPsi`, `iPsiPsiSq`, `iPsiSqPsi` and
the difference moments of `iPsiCubePsi`, `iPsiSqPsiSq`, `iPsiCubePsiSq`, in the form taken as
hypotheses by the Cauchy argument for the BPHZ models. They hold by `bphzCauchyMoments_holds`. -/
structure BphzCauchyMoments (N : ℕ) (κ : Kappa) : Prop where
  iPsiPsi : PiMomentCanonical.{u} N κ Symbol.iPsiPsi
  iPsiPsi_sub : PiMomentCanonicalSub.{u} N κ Symbol.iPsiPsi
  iPsiPsiSq : PiMomentCanonical.{u} N κ Symbol.iPsiPsiSq
  iPsiPsiSq_sub : PiMomentCanonicalSub.{u} N κ Symbol.iPsiPsiSq
  iPsiSqPsi : PiMomentCanonical.{u} N κ Symbol.iPsiSqPsi
  iPsiSqPsi_sub : PiMomentCanonicalSub.{u} N κ Symbol.iPsiSqPsi
  iPsiCubePsi_sub : PiMomentModelSub.{u} N κ Symbol.iPsiCubePsi
  iPsiSqPsiSq_sub : PiMomentModelSub.{u} N κ Symbol.iPsiSqPsiSq
  iPsiCubePsiSq_sub : PiMomentModelSub.{u} N κ Symbol.iPsiCubePsiSq

/-- Uniform single `Π`-bound for the canonical models with Hairer's constants, symbol `i`. -/
def PiSingleBound (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar : ℝ) (q : ℕ)
    (i : Symbol) (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ},
    IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
    (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) →
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ∫⁻ ω, ‖(canonicalModelOfLift N κ
          ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
          (ξ ω)).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
          parabolicSemigroup.order)) ^ q

/-- Uniform difference `Π`-bound for the canonical models with Hairer's constants (two
mollifiers), symbol `i`. -/
def PiSubBound (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar θ : ℝ) (q : ℕ)
    (i : Symbol) (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
    IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
    IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
    (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ∫⁻ ω, ‖(canonicalModelOfLift N κ
          ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
          (ξ ω)).regPi x (Pi.single i 1) t x -
        (canonicalModelOfLift N κ
          ((hairerWickConstant N ρ' ε', hairerSunsetConstant N ρ' ε') : RenormalisationConstants)
          (ξ' ω)).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * (max ε ε') ^ θ * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
          parabolicSemigroup.order)) ^ q

end RegularityStructures.Phi43

end

public section

universe u

namespace RegularityStructures.Phi43

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ} {i : Symbol}
  {C C' : ℝ}

theorem PiSingleBound.mono (h : PiSingleBound.{u} N ρ κ κbar q i C) (hC : C ≤ C') :
    PiSingleBound.{u} N ρ κ κbar q i C' := by
  intro Ω _ P W ε ξ hW hε hξ hgr t ht x
  refine le_ofReal_pow_mono (h hW hε hξ hgr t ht x) ?_
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _)

theorem PiSubBound.mono (h : PiSubBound.{u} N ρ ρ' κ κbar θ q i C) (hC : C ≤ C') :
    PiSubBound.{u} N ρ ρ' κ κbar θ q i C' := by
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' hgr hgr' t ht x
  refine le_ofReal_pow_mono (h hW hε hε' hξ hξ' hgr hgr' t ht x) ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _)) (Real.rpow_nonneg ht.1.le _)

end RegularityStructures.Phi43

end
