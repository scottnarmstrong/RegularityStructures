/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.RandomCanonicalModel
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
import Mathlib.Tactic

/-!
# Whole-space continuity of the regularised fields of the canonical models

For the canonical renormalised model, `(t, y) ↦ (Q_t Π_x e_i)(y)` is continuous on `t > 0`
(`continuousOn_regPi_canonicalRenormalisedModel`): by `regPi_single_canonicalRenormalisedModel_eq_sum`
it is a finite sum of constants times `Q_t(basis_τ)`, each jointly continuous by
`continuousOn_semigroup_apply` (polynomial growth of the global basis).  This gives
`IsContinuousRandomModelWithFieldsOn` for the family `canonicalModelOfLift`; the zero-noise branch is
`canonicalRenormalisedModel` of the zero noise, covered by the same lemma.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem continuousOn_regPi_canonicalRenormalisedModel (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (x : ParabolicSpace) (i : Symbol) :
    ContinuousOn (fun w : ℝ × ParabolicSpace =>
      (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ)
        w.1 w.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hsum : ContinuousOn (fun w : ℝ × ParabolicSpace => ∑ τ : Symbol, structureGroupMap
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x) (basis i) τ *
        parabolicSemigroup.apply w.1
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C τ) w.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ fun τ _ => ?_
    refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_semigroup_apply (renormalisedExtensionGlobalBasis_growth N κ noise hf C τ)
      (renormalisedExtensionGlobalBasis_smooth N κ noise C τ).continuous
  refine hsum.congr fun w hw => ?_
  exact regPi_single_canonicalRenormalisedModel_eq_sum N κ noise Cg q hg C x i hw.1 w.2

theorem continuousOn_regPi_canonicalModelOfLift {N : ℕ} {κ : Kappa} {C : RenormalisationConstants}
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (i : Symbol) (x : ParabolicSpace) :
    ContinuousOn (fun w : ℝ × ParabolicSpace =>
      (canonicalModelOfLift N κ C f).regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) w.1 w.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.univ) := by
  obtain ⟨Cg, q, hg', hE⟩ := canonicalModelOfLift_eq (N := N) (κ := κ) (C := C) hf hg
  simp only [hE]
  exact (continuousOn_regPi_canonicalRenormalisedModel N κ _ Cg q hg' C x i).mono
    (Set.prod_mono (fun t ht => ht.1) (Set.subset_univ _))

theorem isContinuousRandomModelWithFieldsOn_canonicalModelOfLift {N : ℕ} {κ : Kappa}
    {C : RenormalisationConstants} {Ω : Type*} [MeasurableSpace Ω]
    {ξ : Ω → SpaceTime → ℝ} (hmeas : ∀ z, Measurable fun ω => ξ ω z)
    (hsm : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    (S : Set ParabolicSpace) :
    RegularityStructures.IsContinuousRandomModelWithFieldsOn (fun ω => canonicalModelOfLift N κ C (ξ ω)) S :=
  ⟨isContinuousRandomModelOn_canonicalModelOfLift hmeas hsm hgr S,
    fun ω i x => continuousOn_regPi_canonicalModelOfLift (hsm ω) (hgr ω) i x⟩

end RegularityStructures.Phi43

end
