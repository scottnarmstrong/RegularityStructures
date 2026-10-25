/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
import RegularityStructures.Abstract.Singular.TwoModel.Poly
import Mathlib.Tactic.Linarith
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Uniqueness of the renormalised canonical model on the negative and integrated core

Hairer [Hai14, Definition 5.9, Section 9.2, Proposition 3.31]. Two models
satisfying the same canonical-model predicate
`Statements.IsRenormalisedCanonicalModel` agree on the whole negative
Q-families, not just at their base points. Admissibility then fixes every
original integrated source. Uniqueness on the positive products is not
asserted here.
-/

public section

namespace RegularityStructures.Phi43

theorem canonicalModels_pi_fMinus_eq (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (τ : Symbol) (hτ : τ ∈ fMinus) (x : ParabolicSpace) :
    Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) := by
  apply Subtype.ext
  funext t z
  by_cases ht : 0 < t
  · exact (hZ.2.1 τ hτ x t ht z).trans (hZ'.2.1 τ hτ x t ht z).symm
  · have hz := parabolicSemigroup.eq_zero_of_nonpos (Z.pi x (Pi.single τ 1)).2 (le_of_not_gt ht)
    have hz' := parabolicSemigroup.eq_zero_of_nonpos (Z'.pi x (Pi.single τ 1)).2 (le_of_not_gt ht)
    rw [hz, hz']

private theorem fMinus_of_source (τ : Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) : τ ∈ fMinus := by
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals simp [fMinus, isFMinus]

theorem canonicalModels_realGerm_source_eq (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (τ : Symbol) (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube)
    (x : ParabolicSpace) : realGermP Z (annKernel0C N) x τ =
      realGermP Z' (annKernel0C N) x τ := by
  have hp := canonicalModels_pi_fMinus_eq N κ noise C Z Z' hZ hZ' τ
    (fMinus_of_source τ hτ) x
  have he : (fun t z => Z.regPi x (Pi.single τ 1) t z) =
      (fun t z => Z'.regPi x (Pi.single τ 1) t z) := by
    exact congrArg Subtype.val hp
  unfold realGermP
  rw [he]

theorem canonicalModels_pi_integrated_source_eq (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (τ : Symbol) (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube)
    (x : ParabolicSpace) :
    Z.pi x (phi43AbstractIntegration (Pi.single τ 1)) =
      Z'.pi x (phi43AbstractIntegration (Pi.single τ 1)) := by
  have hneg := (homogeneity_neg_iff_isFMinus κ τ).2
    ((mem_fMinus_iff_isFMinus τ).1 (fMinus_of_source τ hτ))
  have hdeg : (phi43RegularityStructure κ).deg τ < gamma κ := by
    have hk := κ.2.1
    change homogeneity κ τ < 1 + 3 * κ.1
    linarith only [hneg, hk]
  have ha : (Pi.single τ 1 : Symbol → ℝ) ∈ phi43IntegrationSector := by
    rcases hτ with rfl | rfl | rfl | rfl
    all_goals intro σ _ _ _ _
    all_goals simp_all
  have hg := canonicalModels_realGerm_source_eq N κ noise C Z Z' hZ hZ' τ hτ x
  apply Subtype.ext
  funext t z
  by_cases ht : 0 < t
  · have h1 := hZ.1.realises x τ hdeg ha t ht z
    have h2 := hZ'.1.realises x τ hdeg ha t ht z
    change Z.regPi x (phi43AbstractIntegration (Pi.single τ 1)) t z =
      Z'.regPi x (phi43AbstractIntegration (Pi.single τ 1)) t z
    rw [h1, h2]
    simp only [realRegP, ite_eq_left ht, hg]
  · have hz := parabolicSemigroup.eq_zero_of_nonpos
      (Z.pi x (phi43AbstractIntegration (Pi.single τ 1))).2 (le_of_not_gt ht)
    have hz' := parabolicSemigroup.eq_zero_of_nonpos
      (Z'.pi x (phi43AbstractIntegration (Pi.single τ 1))).2 (le_of_not_gt ht)
    rw [hz, hz']

end RegularityStructures.Phi43

end
