/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyMomentDefs
public import Phi43.BPHZ.PolynomialPiBounds
public import Phi43.BPHZ.ModelRegPiPsiMoment
public import Phi43.BPHZ.ModelRegPiTreesNoise
public import Phi43.BPHZ.ModelRegPiTreesI
public import Phi43.BPHZ.ModelRegPiPsiSqXMoments
public import Phi43.BPHZ.PositivePiMomentPsiX
public import Phi43.BPHZ.PositivePiMomentSq
public import Phi43.BPHZ.PositivePiMomentCubeSq
import Mathlib.Tactic

/-!
# Single-model `Π`-moments of the canonical models, symbol by symbol

For every symbol `i ∉ Dπ` below `γ = 1 + 3κ`, the uniform single bound `PiSingleBound` for the
canonical models `canonicalModelOfLift N κ (hairerWickConstant, hairerSunsetConstant) (ξ ω)`
(`exists_piSingleBound_noise`, …, `exists_piSingleBound_iPsiCubeSq`); `exists_piSingleBound_all`
in `Phi43.BPHZ.BphzCauchyPiAll` takes one constant `C₀` for all symbols.
The symbols `iPsiPsi`, `iPsiPsiSq`, `iPsiSqPsi` are taken from `BphzCauchyMoments`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ}

/-- From a moment bound for arbitrary `IsPhi43ModelOf` families to the uniform bound for the
canonical models. -/
theorem exists_piSingleBound_of_model {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
            parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q i C := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun {Ω _ P W ε ξ} hW hε hξ hgr t ht x => ?_⟩
  exact h (fun ω => canonicalModelOfLift N κ
    ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (ξ ω))
    hW hε hξ (Filter.Eventually.of_forall fun ω =>
      canonicalModelOfLift_isPhi43ModelOf (hξ.1 ω) (hgr ω)) t ht x

/-- From a moment bound for the canonical models to the uniform bound. -/
theorem exists_piSingleBound_of_canonical {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ Cst = hairerWickConstant N ρ ε → (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
            parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q i C := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun hW hε hξ hgr t ht x =>
    h hW hε hξ rfl (Filter.Eventually.of_forall hgr) t ht x⟩

private theorem kappa_half_le : κ.1 / 2 ≤ κ.1 := by linarith [κ.2.1]

private theorem canonical_of_noC {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg i + κbar) /
            parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q i C := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun hW hε hξ hgr t ht x =>
    h hW hε hξ (Filter.Eventually.of_forall hgr) t ht x⟩

variable (hρ : IsMollifier ρ) (hκb : κbar ≤ κ.1 / 2) (hq : 1 ≤ q)

include hρ hκb hq

theorem exists_piSingleBound_noise :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.noise C :=
  exists_piSingleBound_of_model (i := Symbol.noise)
    (Phi43.regPi_noise_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) hq)

theorem exists_piSingleBound_psi :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.psi C :=
  exists_piSingleBound_of_model (i := Symbol.psi)
    (Phi43.regPi_psi_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) hq)

theorem exists_piSingleBound_psiSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.psiSq C :=
  exists_piSingleBound_of_model (i := Symbol.psiSq)
    (Phi43.regPi_psiSq_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) hq)

theorem exists_piSingleBound_psiCube :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.psiCube C :=
  exists_piSingleBound_of_model (i := Symbol.psiCube)
    (Phi43.regPi_psiCube_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) hq)

theorem exists_piSingleBound_psiSqX (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q (Symbol.psiSqX k) C :=
  exists_piSingleBound_of_model (i := Symbol.psiSqX k)
    (Phi43.regPi_psiSqX_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) hq k)

theorem exists_piSingleBound_iPsiCubePsi :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubePsi C :=
  exists_piSingleBound_of_model (i := Symbol.iPsiCubePsi)
    (Phi43.regPi_iPsiCubePsi_lintegral_enorm_pow_le N hρ κ hκb hq)

theorem exists_piSingleBound_iPsiSqPsiSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiSqPsiSq C :=
  exists_piSingleBound_of_model (i := Symbol.iPsiSqPsiSq)
    (Phi43.regPi_iPsiSqPsiSq_lintegral_enorm_pow_le N hρ κ hκb hq)

theorem exists_piSingleBound_iPsiCubePsiSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubePsiSq C :=
  exists_piSingleBound_of_model (i := Symbol.iPsiCubePsiSq)
    (Phi43.regPi_iPsiCubePsiSq_lintegral_enorm_pow_le N hρ κ hκb hq)

theorem exists_piSingleBound_psiX (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q (Symbol.psiX k) C :=
  canonical_of_noC (regPi_psiX_lintegral_enorm_pow_le N hρ κ (hκb.trans kappa_half_le) k hq)

theorem exists_piSingleBound_iPsiSq (hκ0 : 0 ≤ κbar) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiSq C :=
  canonical_of_noC (regPi_iPsiSq_lintegral_enorm_pow_le N hρ κ hκ0 hκb hq)

theorem exists_piSingleBound_iPsiCube (hκ0 : 0 ≤ κbar) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiCube C :=
  exists_piSingleBound_of_canonical (regPi_iPsiCube_lintegral_enorm_pow_le N hρ κ hκ0 hκb hq)

theorem exists_piSingleBound_iPsiCubeSq (hκ0 : 0 ≤ κbar) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubeSq C :=
  exists_piSingleBound_of_canonical (regPi_iPsiCubeSq_lintegral_enorm_pow_le N hρ κ hκ0 hκb hq)

end RegularityStructures.Phi43

end
