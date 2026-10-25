/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.MeasurableTreeFunctions
public import Phi43.BPHZ.MeasurableGroupAction
import Mathlib.Tactic

/-!
# Measurability in `ω` of the corrected characters

For a measurable family of noises, the five components of the corrected character
`renormalisedExtensionCharacter C x` of the canonical data are measurable in `ω`
(`measurable_extensionCharacter_shift`, …, `measurable_extensionCharacter_cPsiCube`), and hence so
are the matrix coefficients of its action (`measurable_extensionCharacter_coeff`) and of the
transition `Γ_{yx}` between two base points (`measurable_extensionGamma_coeff`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {κ : Kappa} {n : Ω → CanonicalNoise}

omit [MeasurableSpace Ω] in
private theorem smooth_globalPsi (ω : Ω) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (hairerCanonicalData (κ := κ) N (n ω)).globalPsi :=
  canonicalGlobalPiBasis_smooth N (κ := κ) (n ω) .psi

private theorem measurable_localPsi_family (hn : NoiseFamilyMeasurable n) :
    Measurable fun q : Ω × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N (n q.1)).localPsi q.2 := by
  have : ∀ ω, (hairerCanonicalData (κ := κ) N (n ω)).localPsi =
      (hairerCanonicalData (κ := κ) N (n ω)).globalPsi := fun ω =>
    CanonicalData.localPsi_eq_globalPsi _
  simp_rw [this]
  exact measurable_globalPsi_uncurry hn

theorem measurable_extensionCharacter_shift (C : RenormalisationConstants) (x : ParabolicSpace)
    (i : Fin 4) :
    Measurable fun ω => ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C
      x).shift i :=
  measurable_const

theorem measurable_extensionCharacter_cPsiGrad (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (x : ParabolicSpace) (i : Fin 3) :
    Measurable fun ω => ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C
      x).cPsiGrad i := by
  have h := measurable_hairerSpatialGradient_apply N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).localPsi) (measurable_localPsi_family (κ := κ) (N := N) hn)
    (fun ω => by
      have : (hairerCanonicalData (κ := κ) N (n ω)).localPsi =
          (hairerCanonicalData (κ := κ) N (n ω)).globalPsi :=
        CanonicalData.localPsi_eq_globalPsi _
      rw [this]; exact smooth_globalPsi ω) i x
  exact h.neg

theorem measurable_extensionCharacter_cPsi (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (x : ParabolicSpace) :
    Measurable fun ω => ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C
      x).cPsi := by
  have h1 := measurable_hairerConvolution_apply N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).localPsi) (measurable_localPsi_family (κ := κ) (N := N) hn) x
  refine h1.neg.add (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul (measurable_extensionCharacter_cPsiGrad hn C x i)

theorem measurable_extensionCharacter_cPsiSq (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (x : ParabolicSpace) :
    Measurable fun ω => ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C
      x).cPsiSq := by
  have hP := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
  have h := measurable_hairerConvolution_apply N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).localPsiSq) (by
      have : ∀ ω, (hairerCanonicalData (κ := κ) N (n ω)).localPsiSq =
          (hairerCanonicalData (κ := κ) N (n ω)).globalPsiSq := fun ω =>
        CanonicalData.localPsiSq_eq_globalPsiSq _
      simp_rw [this]
      exact hP.mul hP) x
  exact h.neg

theorem measurable_extensionCharacter_cPsiCube (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (x : ParabolicSpace) :
    Measurable fun ω => ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C
      x).cPsiCube := by
  have hP := measurable_globalPsi_uncurry (κ := κ) (N := N) hn
  have h := measurable_hairerConvolution_apply N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).localPsiCube) (by
      have : ∀ ω, (hairerCanonicalData (κ := κ) N (n ω)).localPsiCube =
          (hairerCanonicalData (κ := κ) N (n ω)).globalPsiCube := fun ω =>
        CanonicalData.localPsiCube_eq_globalPsiCube _
      simp_rw [this]
      exact (hP.mul hP).mul hP) x
  have hI := measurable_hairerConvolution_apply N
    (Y := fun ω => (hairerCanonicalData (κ := κ) N (n ω)).globalPsi) (measurable_globalPsi_uncurry
      (κ := κ) (N := N) hn) x
  exact h.neg.add (hI.const_mul _)

/-- Matrix coefficients of the corrected character are measurable in `ω`. -/
theorem measurable_extensionCharacter_coeff (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (x : ParabolicSpace) (τ σ : Symbol) :
    Measurable fun ω => structureGroupMap
      ((hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionCharacter C x) (basis τ) σ :=
  measurable_structureGroupMap_basis _ (measurable_extensionCharacter_shift C x)
    (measurable_extensionCharacter_cPsi hn C x) (measurable_extensionCharacter_cPsiGrad hn C x)
    (measurable_extensionCharacter_cPsiSq hn C x) (measurable_extensionCharacter_cPsiCube hn C x)
    τ σ

/-- Matrix coefficients of the transition `Γ_{yx}` are measurable in `ω`. -/
theorem measurable_extensionGamma_coeff (hn : NoiseFamilyMeasurable n)
    (C : RenormalisationConstants) (y x : ParabolicSpace) (τ σ : Symbol) :
    Measurable fun ω => (hairerCanonicalData (κ := κ) N (n ω)).renormalisedExtensionGamma C y x
      (basis τ) σ :=
  measurable_inv_mul_components _ _ (measurable_extensionCharacter_shift C y)
    (measurable_extensionCharacter_cPsi hn C y) (measurable_extensionCharacter_cPsiGrad hn C y)
    (measurable_extensionCharacter_cPsiSq hn C y) (measurable_extensionCharacter_cPsiCube hn C y)
    (measurable_extensionCharacter_shift C x) (measurable_extensionCharacter_cPsi hn C x)
    (measurable_extensionCharacter_cPsiGrad hn C x) (measurable_extensionCharacter_cPsiSq hn C x)
    (measurable_extensionCharacter_cPsiCube hn C x) τ σ

end RegularityStructures.Phi43

end
