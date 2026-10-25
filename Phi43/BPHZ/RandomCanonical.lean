/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.RandomCanonicalModification
public import Phi43.BPHZ.CanonicalBridgeData
import Mathlib.Tactic

/-!
# The canonical model of a lifted noise, as a function of the noise

`canonicalModelOfLift N κ C f` is the renormalised canonical model of the periodic lift of the
smooth function `f` when `f` is smooth with the polynomial growth of `HasPhi43NoiseGrowth`
(`canonicalRenormalisedModel`), and `zeroPhi43Model` otherwise.  Its entries are explicit
functions of the noise, which is what the measurability in `ω` (`IsContinuousRandomModelOn`) needs.

`exists_canonical_modification`: for a regularised noise with almost surely polynomial growth there
is a modification `ξ'` of `ξ` (equal on a measurable set `G` of full measure, zero off `G`) such that
for EVERY `ω`, `canonicalModelOfLift N κ C (ξ' ω)` satisfies `IsPhi43ModelOf` for `ξ' ω`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The renormalised canonical model of the lift of `f`, if `f` is smooth with polynomial growth
of its derivatives of order `≤ 4`; the model of the zero noise otherwise. -/
def canonicalModelOfLift (N : ℕ) (κ : Kappa) (C : RenormalisationConstants)
    (f : SpaceTime → ℝ) : Model (phi43RegularityStructure κ) parabolicSemigroup := by
  classical
  exact if h : IsSmoothOnSpaceTime f ∧ Statements.HasPhi43NoiseGrowth f then
    canonicalRenormalisedModel N κ (canonicalNoiseOfSpaceTime f h.1) (Classical.choose h.2)
      (Classical.choose (Classical.choose_spec h.2))
      (Classical.choose_spec (Classical.choose_spec h.2)) C
  else zeroPhi43Model N κ C

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

theorem canonicalModelOfLift_isRenormalisedCanonicalModel (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    Statements.IsRenormalisedCanonicalModel N κ (canonicalNoiseOfSpaceTime f hf) C
      (canonicalModelOfLift N κ C f) := by
  unfold canonicalModelOfLift
  split_ifs with h
  · exact canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ _ _ _ _ C
  · exact absurd ⟨hf, hg⟩ h

theorem canonicalModelOfLift_isPhi43ModelOf (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    Statements.IsPhi43ModelOf N κ f C (canonicalModelOfLift N κ C f) :=
  ⟨canonicalNoiseOfSpaceTime f hf, fun _ => rfl,
    canonicalModelOfLift_isRenormalisedCanonicalModel hf hg⟩

theorem hasPhi43NoiseGrowth_zero : Statements.HasPhi43NoiseGrowth (fun _ : SpaceTime => (0 : ℝ)) :=
  ⟨0, 0, fun k _ z => by
    have : (fun w : ParabolicSpace => (fun _ : SpaceTime => (0 : ℝ)) (w.1, torusProj w.2)) =
        fun _ => (0 : ℝ) := rfl
    rw [this, iteratedFDeriv_fun_zero]
    simp⟩

/-- **A canonical modification of a regularised noise**: off a null set the noise is replaced
by `0`; for every `ω` the canonical model of the lift of the modified noise satisfies
`IsPhi43ModelOf` (so also `IsRandomPhi43Model`). -/
theorem exists_canonical_modification {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgrowth : ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) :
    ∃ (ξ' : Ω → SpaceTime → ℝ) (G : Set Ω), MeasurableSet G ∧ P Gᶜ = 0 ∧
      IsRegularisedNoise P W ρ ε ξ' ∧ (∀ ω ∈ G, ξ' ω = ξ ω) ∧
      (∀ ω, IsSmoothOnSpaceTime (ξ' ω) ∧ Statements.HasPhi43NoiseGrowth (ξ' ω)) ∧
      (∀ ω, Statements.IsPhi43ModelOf N κ (ξ' ω) C (canonicalModelOfLift N κ C (ξ' ω))) ∧
      IsRandomPhi43Model N κ ξ' C (fun ω => canonicalModelOfLift N κ C (ξ' ω)) := by
  classical
  obtain ⟨G, hGm, hG, hGz⟩ := exists_measurableSet_of_ae hgrowth
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    exact hGz
  have hsm : ∀ ω, IsSmoothOnSpaceTime (G.piecewise ξ (fun _ => (0 : SpaceTime → ℝ) ) ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]; exact hξ.1 ω
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω]; exact contDiff_const
  have hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (G.piecewise ξ (fun _ => (0 : SpaceTime → ℝ)) ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]; exact hG ω hω
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω]; exact hasPhi43NoiseGrowth_zero
  have hreg : IsRegularisedNoise P W ρ ε (G.piecewise ξ (fun _ => (0 : SpaceTime → ℝ))) := by
    refine ⟨hsm, fun z => ⟨?_, ?_⟩⟩
    · have e : (fun ω => G.piecewise ξ (fun _ => (0 : SpaceTime → ℝ)) ω z) =
          G.piecewise (fun ω => ξ ω z) (fun _ => (0 : ℝ)) := by
        funext ω
        by_cases hω : ω ∈ G <;> simp [Set.piecewise, hω]
      rw [e]
      exact Measurable.piecewise hGm (hξ.2 z).1 measurable_const
    · filter_upwards [hGae, (hξ.2 z).2] with ω hω h2
      rw [Set.piecewise_eq_of_mem _ _ _ hω]; exact h2
  refine ⟨G.piecewise ξ (fun _ => 0), G, hGm, hGz, hreg, fun ω hω => ?_,
    fun ω => ⟨hsm ω, hgr ω⟩, fun ω => canonicalModelOfLift_isPhi43ModelOf (hsm ω) (hgr ω),
    fun ω => ?_⟩
  · exact Set.piecewise_eq_of_mem _ _ _ hω
  · obtain ⟨noise, hn, hcan⟩ := canonicalModelOfLift_isPhi43ModelOf (N := N) (κ := κ) (C := C)
      (hsm ω) (hgr ω)
    obtain ⟨Cg, q, hg⟩ := hgr ω
    have hzeta : noise.zeta = fun w : ParabolicSpace =>
        G.piecewise ξ (fun _ => (0 : SpaceTime → ℝ)) ω (w.1, torusProj w.2) := funext hn
    refine ⟨hsm ω, noise, fun z => hn z, ⟨Cg, q, fun k hk z => ?_⟩, hcan⟩
    rw [hzeta]; exact hg k hk z

end RegularityStructures.Phi43

end
