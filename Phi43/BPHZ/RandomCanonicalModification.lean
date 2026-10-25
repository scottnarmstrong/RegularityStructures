/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaEntries
public import Phi43.Structure.CanonicalModelExistence
public import Phi43Statements.Defs.IsPhi43ModelOf
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import Phi43.Mollifier
import Mathlib.Tactic

/-!
# From "almost surely" to "every `ω`"

The Kolmogorov bound for the model norms quantifies over every `ω`, while the models of the Cauchy
statement for the BPHZ models are only given almost surely. The ingredients for modifying a noise
and its models on a null set are:

* `exists_measurableSet_of_ae`: an almost sure property holds on a measurable set `G` of full
  measure;
* `zeroCanonicalNoise`, `zeroCanonicalNoise_growth`: the zero noise, with polynomial growth of its
  derivatives;
* `zeroPhi43Model`: the renormalised canonical model of the zero noise, which satisfies
  `IsRenormalisedCanonicalModel` for the zero noise and any constants `C`.

The modification itself (the noise set to `0` off `G`) is carried out in
`Phi43.BPHZ.RandomCanonical`. The almost sure growth of the regularised noise is an input there
(it is not a consequence of `IsRegularisedNoise`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- An almost sure property holds on a measurable set of full measure. -/
theorem exists_measurableSet_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ ω ∈ G, p ω) ∧ P Gᶜ = 0 := by
  obtain ⟨t, hts, htm, htz⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨tᶜ, htm.compl, fun ω hω => ?_, by rwa [compl_compl]⟩
  by_contra hp
  exact hω (hts hp)

end RegularityStructures.Phi43

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The zero noise. -/
def zeroCanonicalNoise : CanonicalNoise where
  zeta := fun _ => 0
  smooth := contDiff_const
  periodic := fun _ _ => rfl

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

theorem zeroCanonicalNoise_growth : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k zeroCanonicalNoise.zeta z‖ ≤ 0 * (1 + parabolicNorm z) ^ 0 := by
  intro k _ z
  have : zeroCanonicalNoise.zeta = fun _ => (0 : ℝ) := rfl
  rw [this, iteratedFDeriv_fun_zero]
  simp

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The renormalised canonical model of the zero noise. -/
def zeroPhi43Model (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) :
    Model (phi43RegularityStructure κ) parabolicSemigroup :=
  canonicalRenormalisedModel N κ zeroCanonicalNoise 0 0 zeroCanonicalNoise_growth C

end RegularityStructures.Phi43

end

