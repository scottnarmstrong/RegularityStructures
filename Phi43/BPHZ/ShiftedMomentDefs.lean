/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyMomentDefs
public import Phi43.BPHZ.GammaFullDet
public import Phi43.BPHZ.PolynomialPiBounds
import Mathlib.Tactic

/-!
# Shifted BPHZ constants: the moment interface

The Cauchy property of the BPHZ models is proved directly for models with constants
`C_K(ρ, ε) + c`, where `C_K(ρ, ε) = (hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε)` and
`‖c‖ ≤ B`, uniformly in the shift `c`. The convergence of the renormalised models then follows
without a Lipschitz bound on the action of the renormalisation group on models.

This file fixes the interface between the two halves of that argument:

* the moment half proves `ShiftedBphzInputs N κ`: shifted analogues of `PiSingleBound`,
  `PiSubBound` and of the Γ-hypotheses of the Kolmogorov bound `kolmogorov_modelNorm`, with the
  difference factor `max ε ε' ^ θ + ‖c - c'‖`;
* the assembly half proves `bphzModels_cauchy_shifted` (and the convergence of the renormalised
  models) from `ShiftedBphzInputs`, the existence and uniqueness of the renormalised canonical
  model, the Kolmogorov bound for the model norms, the Cauchy property of the noises and the
  comparison of the renormalisation constants.

Here `‖c‖` is the norm of `RenormalisationConstants = ℝ × ℝ`, the max norm.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

universe u

/-- The BPHZ constants with Hairer's kernel, shifted by `c`. -/
noncomputable def shiftConst (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (c : RenormalisationConstants) : RenormalisationConstants :=
  ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) + c

/-- Uniform single `Π`-bound, symbol `i`, for the canonical models with shifted constants. -/
def PiShiftSingleBound (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar : ℝ) (q : ℕ)
    (i : Symbol) (B C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (c : RenormalisationConstants), ‖c‖ ≤ B →
    IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
    (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) →
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ∫⁻ ω, ‖(canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).regPi x
          (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
          parabolicSemigroup.order)) ^ q

/-- Uniform difference `Π`-bound, symbol `i`, for two canonical models with shifted constants
(two mollifiers, two shifts). -/
def PiShiftSubBound (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar θ : ℝ) (q : ℕ)
    (i : Symbol) (B C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (c c' : RenormalisationConstants),
    ‖c‖ ≤ B → ‖c'‖ ≤ B →
    IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
    IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
    (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ∫⁻ ω, ‖(canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).regPi x
          (Pi.single i 1) t x -
        (canonicalModelOfLift N κ (shiftConst N ρ' ε' c') (ξ' ω)).regPi x
          (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * ((max ε ε') ^ θ + ‖c - c'‖) *
          t ^ (((phi43RegularityStructure κ).deg i + κbar) / parabolicSemigroup.order)) ^ q

/-- The random Γ-entry bounds (single, for both models, and difference) in the shape of the
Γ-hypotheses of `kolmogorov_modelNorm`, for two canonical models with shifted constants. -/
def GammaShiftBounds (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar θ : ℝ) (q : ℕ)
    (B C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (c c' : RenormalisationConstants),
    ‖c‖ ≤ B → ‖c'‖ ≤ B →
    IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
    IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
    (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
    (∀ i j, (i, j) ∉ gammaFullDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
        (phi43RegularityStructure κ).deg j < (phi43RegularityStructure κ).deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).gammaMap y x
            (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            ((phi43RegularityStructure κ).deg i - (phi43RegularityStructure κ).deg j +
              κbar)) ^ q) ∧
    (∀ i j, (i, j) ∉ gammaFullDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
        (phi43RegularityStructure κ).deg j < (phi43RegularityStructure κ).deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ (shiftConst N ρ' ε' c') (ξ' ω)).gammaMap y x
            (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            ((phi43RegularityStructure κ).deg i - (phi43RegularityStructure κ).deg j +
              κbar)) ^ q) ∧
    (∀ i j, (i, j) ∉ gammaFullDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
        (phi43RegularityStructure κ).deg j < (phi43RegularityStructure κ).deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).gammaMap y x
              (Pi.single i 1) j -
            (canonicalModelOfLift N κ (shiftConst N ρ' ε' c') (ξ' ω)).gammaMap y x
              (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * ((max ε ε') ^ θ + ‖c - c'‖) * parabolicSemigroup.scaleDist y x ^
            ((phi43RegularityStructure κ).deg i - (phi43RegularityStructure κ).deg j +
              κbar)) ^ q)

/-- The moment inputs for the shifted BPHZ models: shifted `Π`-bounds for every non-polynomial
symbol below `gamma κ`, and the shifted Γ-entry bounds, uniformly in the shift `‖c‖ ≤ B`. The
parameter constraints are those of the unshifted Cauchy argument for the BPHZ models. -/
structure ShiftedBphzInputs (N : ℕ) (κ : Kappa) : Prop where
  pi : ∀ {ρ : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → ∀ {κbar : ℝ}, 0 ≤ κbar → κbar ≤ κ.1 / 2 →
    ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
      PiShiftSingleBound.{u} N ρ κ κbar q i B C₀
  pi_sub : ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
    0 ≤ κbar → 0 < θ → κbar + θ ≤ κ.1 / 2 → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
      PiShiftSubBound.{u} N ρ ρ' κ κbar θ q i B C₀
  gamma : ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
    0 ≤ κbar → κbar ≤ κ.1 / 2 → 0 < θ → θ < κ.1 - κbar → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ GammaShiftBounds.{u} N ρ ρ' κ κbar θ q B C₀

end RegularityStructures.Phi43

end
