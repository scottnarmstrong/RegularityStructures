/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedCanonicalModel
public import Phi43.Structure.RenormalisedGammaGrowth
public import Phi43.Structure.RenormalisedGrowthWeightedBounds
public import Phi43.Structure.QuadraticModelRealising
public import Phi43.Structure.CanonicalJointMeasurable
public import Phi43.Structure.RenormalisedGammaBounds
public import Phi43.Structure.RenormalisedExtensionPiBounds
import Mathlib.Tactic.Linarith
public import Phi43.Structure.EnlargedIntegrationExtensionF
public import RegularityStructures.Abstract.IntExt.Bounds
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Probability.ModelKolmogorovQFamilyWeightedSemigroup

/-!
# The enlarged corrected smooth model

The old model is the explicit corrected lift from Hairer (9.3)--(9.5).  The
finite planted completion is then formed by the abstract integration-extension
construction.  The source sector is used for the extension hypothesis because
the raw noise symbol is below the abstract `-2` cutoff; the resulting model
realises the lifted source sector and retains the full degree-≤2 polynomial
sector in the target structure.

This file proves the algebraic extension, its inherited weighted and compact
bounds, and its exact restriction to the old model.  No arbitrary `Pi` field
or analytic-bound container is an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open RegularityStructures
open RegularityStructures.IntExt

namespace RegularityStructures.Phi43

theorem phi43RenormalisedSourceSector_growth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    ∃ C' C'' r s : ℝ, ∃ ρP ρG : ParabolicSpace → ℝ,
      (canonicalRenormalisedModel N κ noise C₀ p hg C).GrowthModel
        (gamma κ) C' C'' ρP ρG r s := by
  obtain ⟨BP, hBP, qP, hP⟩ :=
    canonicalRenormalisedModel_piBoundGrowth N κ noise C₀ p hg C
  obtain ⟨BG, hBG, rG, qG, hG⟩ :=
    canonicalRenormalisedModel_gammaBoundGrowth N κ noise C₀ p hg C
  let m : ℕ := max qP rG
  have hmP : qP ≤ m := Nat.le_max_left _ _
  have hmG : rG ≤ m := Nat.le_max_right _ _
  have hG' : (canonicalRenormalisedModel N κ noise C₀ p hg C).GammaBoundGrowth
      (gamma κ) BG (parabolicPolynomialWeight (m : ℝ)) (qG : ℝ) := by
    intro i j hi hj x y
    have hpow : (1 + parabolicNorm x) ^ rG ≤ (1 + parabolicNorm x) ^ m :=
      pow_le_pow_right₀ (by linarith [parabolicNorm_nonneg x]) hmG
    have hweight : parabolicPolynomialWeight (rG : ℝ) x ≤
        parabolicPolynomialWeight (m : ℝ) x := by
      simpa only [parabolicPolynomialWeight, Real.rpow_natCast] using hpow
    have h1 : BG * parabolicPolynomialWeight (rG : ℝ) x ≤
        BG * parabolicPolynomialWeight (m : ℝ) x :=
      mul_le_mul_of_nonneg_left hweight hBG
    have h2 : 0 ≤ (1 + parabolicNorm (y - x)) ^ (qG : ℝ) :=
      Real.rpow_nonneg (by linarith [parabolicNorm_nonneg (y - x)]) _
    have h3 : 0 ≤ parabolicNorm (y - x) ^
        ((phi43RegularityStructure κ).deg i -
          (phi43RegularityStructure κ).deg j) :=
      Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _
    exact (hG i j hi hj x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3)
  refine ⟨BP, BG, (m : ℝ), (qG : ℝ),
    parabolicPolynomialWeight (m : ℝ), parabolicPolynomialWeight (m : ℝ), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hG', hBP⟩
  · dsimp [gamma]
    linarith [κ.2.1]
  · exact isModerateWeight_parabolicPolynomial (by positivity)
  · exact isModerateWeight_parabolicPolynomial (by positivity)
  · exact_mod_cast (Nat.zero_le qG)
  · intro i hi t ht x
    have hp := hP i hi t ht x
    have hpow : (1 + parabolicNorm x) ^ qP ≤ (1 + parabolicNorm x) ^ m :=
      pow_le_pow_right₀ (by linarith [parabolicNorm_nonneg x]) hmP
    have hweight : (1 + parabolicNorm x) ^ qP ≤
        parabolicPolynomialWeight (m : ℝ) x := by
      simpa only [parabolicPolynomialWeight, Real.rpow_natCast] using hpow
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight hBP)
      (Real.rpow_nonneg ht.1.le _))

theorem phi43RenormalisedSourceSector_intExtHyp
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    IntExtHyp (canonicalRenormalisedModel N κ noise C₀ p hg C)
      (phi43IntegrationExtensionF κ) (annKernel0C N) N (gamma κ)
      phi43SourceSectorSpace := by
  exact phi43SourceSector_intExtHyp_of N κ
    (canonicalRenormalisedModel N κ noise C₀ p hg C)
    (canonicalRenormalisedModel_isRealising_quadratic N κ noise C₀ p hg C)
    (phi43RenormalisedSourceSector_growth N κ noise C₀ p hg C)

/-- The corrected smooth model on the enlarged planted completion. -/
def phi43EnlargedRenormalisedModel
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    Model (phi43RegularityStructureF κ) parabolicSemigroup :=
  (phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C).intExtendOfJoint
    (canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C)

theorem phi43EnlargedRenormalisedModel_isRealising
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).IsRealisingP
      (annKernel0C N) (gamma κ) (phi43PolynomialSectorF κ) phi43IntegrationF
      (IntExt.liftedSector SymbolF.old phi43SourceSectorSpace phi43PlantD) := by
  let M := canonicalRenormalisedModel N κ noise C₀ p hg C
  let H := phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C
  let hJ := canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C
  have h := phi43SourceSector_isRealising_of N κ M H hJ
  simpa only [phi43EnlargedRenormalisedModel, M, H, hJ,
    IntExtHyp.intExtendOfJoint] using h

theorem phi43EnlargedRenormalisedModel_isJointMeasurable
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).IsJointMeasurable := by
  let M := canonicalRenormalisedModel N κ noise C₀ p hg C
  let H := phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C
  let hJ := canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C
  have h := IntExtHyp.isJointMeasurable_intExtend
    (H := H) (H.intExtMeas_of_isJointMeasurable hJ) hJ
  simpa only [phi43EnlargedRenormalisedModel, M, H, hJ,
    IntExtHyp.intExtendOfJoint] using h

theorem phi43EnlargedRenormalisedModel_growthModel
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    ∃ C' C'' r s : ℝ, ∃ ρP ρG : ParabolicSpace → ℝ,
      (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).GrowthModel
        (gamma κ) C' C'' ρP ρG r s := by
  let M := canonicalRenormalisedModel N κ noise C₀ p hg C
  let H := phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C
  let hJ := canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C
  obtain ⟨C', C'', r, s, ρP, ρG, hG⟩ :=
    phi43RenormalisedSourceSector_growth N κ noise C₀ p hg C
  have h := H.growthModel_intExtend
    (H.intExtMeas_of_isJointMeasurable hJ) (phi43_gamma_le_plant κ) hG
  refine ⟨C', C'', r, s, ρP, ρG, ?_⟩
  simpa only [phi43EnlargedRenormalisedModel, M, H, hJ,
    IntExtHyp.intExtendOfJoint] using h

theorem phi43EnlargedRenormalisedModel_regPi_old
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) (x : ParabolicSpace) (a : Symbol → ℝ)
    (t : ℝ) (z : ParabolicSpace) :
    (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).regPi x
        (phi43OldEmbF a) t z =
      (canonicalRenormalisedModel N κ noise C₀ p hg C).regPi x a t z := by
  let M := canonicalRenormalisedModel N κ noise C₀ p hg C
  let H := phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C
  let hJ := canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C
  have hmeas := H.intExtMeas_of_isJointMeasurable hJ
  have hEmb : phi43OldEmbF a = IntExt.liftOld SymbolF.old a := by
    funext τ
    cases τ with
    | old τ =>
        change a τ = IntExt.liftOld SymbolF.old a (.old τ)
        rw [IntExt.liftOld_apply_old (fun _ _ h => SymbolF.old.inj h)]
    | planted τ =>
        change 0 = IntExt.liftOld SymbolF.old a (.planted τ)
        rw [IntExt.liftOld_apply_of_notMem]
        exact fun i h => by cases h
  rw [hEmb]
  change (H.intExtend hmeas).regPi x (IntExt.liftOld SymbolF.old a) t z = _
  have hh := H.intExtend_regPi_liftOld hmeas x a t z
  rw [phi43IntegrationExtensionF_old_eq κ] at hh
  simpa only [phi43EnlargedRenormalisedModel, M, H, hJ,
    IntExtHyp.intExtendOfJoint] using hh

theorem phi43EnlargedRenormalisedModel_gammaMap_old
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) (x y : ParabolicSpace) (a : Symbol → ℝ) :
    (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).gammaMap x y
        (phi43OldEmbF a) =
      phi43OldEmbF ((canonicalRenormalisedModel N κ noise C₀ p hg C).gammaMap x y a) := by
  let M := canonicalRenormalisedModel N κ noise C₀ p hg C
  let H := phi43RenormalisedSourceSector_intExtHyp N κ noise C₀ p hg C
  let hJ := canonicalRenormalisedModel_isJointMeasurable N κ noise C₀ p hg C
  have hmeas := H.intExtMeas_of_isJointMeasurable hJ
  have hEmb : phi43OldEmbF a = IntExt.liftOld SymbolF.old a := by
    funext τ
    cases τ with
    | old τ =>
        change a τ = IntExt.liftOld SymbolF.old a (.old τ)
        rw [IntExt.liftOld_apply_old (fun _ _ h => SymbolF.old.inj h)]
    | planted τ =>
        change 0 = IntExt.liftOld SymbolF.old a (.planted τ)
        rw [IntExt.liftOld_apply_of_notMem]
        exact fun i h => by cases h
  have hh := H.intExtend_gammaMap_liftOld hmeas x y a
  rw [phi43IntegrationExtensionF_old_eq κ] at hh
  have hEmb' : IntExt.liftOld SymbolF.old
      (M.gammaMap x y a) =
      phi43OldEmbF (M.gammaMap x y a) := by
    funext τ
    cases τ with
    | old τ =>
        rw [IntExt.liftOld_apply_old (fun _ _ h => SymbolF.old.inj h)]
        rfl
    | planted τ =>
        rw [IntExt.liftOld_apply_of_notMem _ (fun i h => by cases h)]
        rfl
  change (H.intExtend hmeas).gammaMap x y (phi43OldEmbF a) =
    phi43OldEmbF (M.gammaMap x y a)
  rw [hEmb]
  exact hh.trans hEmb'

theorem phi43EnlargedRenormalisedModel_restrict_old
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C₀ : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C₀ * (1 + parabolicNorm z) ^ p)
    (C : RenormalisationConstants) :
    (∀ x (a : Symbol → ℝ) t z,
      (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).regPi x
          (phi43OldEmbF a) t z =
        (canonicalRenormalisedModel N κ noise C₀ p hg C).regPi x a t z) ∧
    (∀ x y (a : Symbol → ℝ),
      (phi43EnlargedRenormalisedModel N κ noise C₀ p hg C).gammaMap x y
          (phi43OldEmbF a) =
        phi43OldEmbF ((canonicalRenormalisedModel N κ noise C₀ p hg C).gammaMap x y a)) := by
  exact ⟨fun x a t z => phi43EnlargedRenormalisedModel_regPi_old
      N κ noise C₀ p hg C x a t z,
    fun x y a => phi43EnlargedRenormalisedModel_gammaMap_old
      N κ noise C₀ p hg C x y a⟩

end RegularityStructures.Phi43

end
