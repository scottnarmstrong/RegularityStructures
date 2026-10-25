/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyMomentDefs
public import Phi43.BPHZ.ModelRegPiTreesDiff
public import Phi43.BPHZ.ModelRegPiXiNoise
public import Phi43.BPHZ.ModelRegPiPsiSqXMoments
public import Phi43.BPHZ.PositivePiMomentPsiX
public import Phi43.BPHZ.PositivePiMomentSq
public import Phi43.BPHZ.PositivePiMomentCubeSq
import Mathlib.Tactic

/-!
# Difference `Π`-moments of the canonical models, symbol by symbol

For every symbol, the uniform difference bound `PiSubBound` for two canonical models with
Hairer's constants for the mollifiers `ρ`, `ρ'` (`exists_piSubBound_*`).  The symbols
`iPsiPsi`, `iPsiPsiSq`, `iPsiSqPsi`, `iPsiCubePsi`, `iPsiSqPsiSq`, `iPsiCubePsiSq` come from
`BphzCauchyMoments`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}

/-- From a difference bound for arbitrary `IsPhi43ModelOf` families to the uniform bound. -/
theorem exists_piSubBound_of_model {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
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
              parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q i C := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun {Ω _ P W ε ε' ξ ξ'} hW hε hε' hξ hξ' hgr hgr' t ht x => ?_⟩
  exact h (fun ω => canonicalModelOfLift N κ
    ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (ξ ω))
    (fun ω => canonicalModelOfLift N κ
    ((hairerWickConstant N ρ' ε', hairerSunsetConstant N ρ' ε') : RenormalisationConstants)
    (ξ' ω)) hW hε hε' hξ hξ'
    (Filter.Eventually.of_forall fun ω => canonicalModelOfLift_isPhi43ModelOf (hξ.1 ω) (hgr ω))
    (Filter.Eventually.of_forall fun ω => canonicalModelOfLift_isPhi43ModelOf (hξ'.1 ω) (hgr' ω))
    t ht x

/-- From a difference bound for the canonical models to the uniform bound. -/
theorem exists_piSubBound_of_canonical {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
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
              parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q i C := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun hW hε hε' hξ hξ' hgr hgr' t ht x =>
    h hW hε hε' hξ hξ' rfl rfl (Filter.Eventually.of_forall hgr)
      (Filter.Eventually.of_forall hgr') t ht x⟩

private theorem canonical_sub_of_noC {i : Symbol}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single i (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg i + κbar) /
              parabolicSemigroup.order)) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q i C := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun hW hε hε' hξ hξ' hgr hgr' t ht x =>
    h hW hε hε' hξ hξ' (Filter.Eventually.of_forall hgr)
      (Filter.Eventually.of_forall hgr') t ht x⟩

private theorem sub_aux1 (h : κbar + θ ≤ κ.1 / 2) : κbar + θ ≤ κ.1 := by linarith [κ.2.1]
private theorem sub_aux2 (hθ : 0 < θ) (h : κbar + θ ≤ κ.1 / 2) : κbar ≤ κ.1 / 2 := by linarith
private theorem sub_aux3 (h : κbar + θ ≤ κ.1 / 2) : θ ≤ κ.1 - κbar := by linarith [κ.2.1]
private theorem sub_aux4 (hκ0 : 0 ≤ κbar) (h : κbar + θ ≤ κ.1 / 2) : θ ≤ κ.1 := by
  linarith [κ.2.1]

variable (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (hκ0 : 0 ≤ κbar) (hθ : 0 < θ)
  (hκθ : κbar + θ ≤ κ.1 / 2) (hq : 1 ≤ q)

include hρ hρ' hκ0 hθ hκθ hq

theorem exists_piSubBound_noise :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.noise C :=
  exists_piSubBound_of_model (i := Symbol.noise)
    (Phi43.regPi_noise_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux1 hκθ) hq)

theorem exists_piSubBound_psi :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.psi C :=
  exists_piSubBound_of_model (i := Symbol.psi)
    (Phi43.regPi_psi_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux1 hκθ) hq)

theorem exists_piSubBound_psiSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.psiSq C :=
  exists_piSubBound_of_model (i := Symbol.psiSq)
    (Phi43.regPi_psiSq_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux1 hκθ) hq)

theorem exists_piSubBound_psiCube :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.psiCube C :=
  exists_piSubBound_of_model (i := Symbol.psiCube)
    (Phi43.regPi_psiCube_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux1 hκθ) hq)

theorem exists_piSubBound_psiSqX (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q (Symbol.psiSqX k) C :=
  exists_piSubBound_of_model (i := Symbol.psiSqX k)
    (Phi43.regPi_psiSqX_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux1 hκθ) hq k)

theorem exists_piSubBound_psiX (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q (Symbol.psiX k) C :=
  canonical_sub_of_noC
    (regPi_psiX_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 hθ (sub_aux3 hκθ) k hq)

theorem exists_piSubBound_iPsiSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiSq C :=
  canonical_sub_of_noC
    (regPi_iPsiSq_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 (sub_aux2 hθ hκθ) hθ (sub_aux4 hκ0 hκθ) hq)

theorem exists_piSubBound_iPsiCube :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCube C :=
  exists_piSubBound_of_canonical
    (regPi_iPsiCube_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 (sub_aux2 hθ hκθ) hθ (sub_aux4 hκ0 hκθ) hq)

theorem exists_piSubBound_iPsiCubeSq :
    ∃ C : ℝ, 0 ≤ C ∧ PiSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCubeSq C :=
  exists_piSubBound_of_canonical
    (regPi_iPsiCubeSq_sub_lintegral_enorm_pow_le N hρ hρ' κ hκ0 (sub_aux2 hθ hκθ) hθ
      (sub_aux4 hκ0 hκθ) hq)

end RegularityStructures.Phi43

end
