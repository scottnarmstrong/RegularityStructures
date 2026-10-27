/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Probability.IndependentComplement
public import GlobalPhi43.Probability.NoiseExteriorApproximation
import Mathlib.Tactic.Linarith

/-! The Gaussian window germ, by independent-complement descent.
All information-field, isometry and exterior-exhaustion inputs are proved
from the supplied white noise; they require no additional assumptions. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures

namespace GlobalPhi43.Flow

open GlobalPhi43.Probability

/-- Exact equality of completed information fields for every deterministic
real start pair, including the zero-length window. The index n corresponds
to m=n+1 in the source intersection over positive integers. -/
theorem noiseWindowSigma_germ {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (s t : ℝ) (_hst : s ≤ t) :
    (⨅ n : ℕ, enlargedNoiseWindowSigma P W s t (1 / ((n : ℝ) + 1))) =
      noiseWindowSigma P W s t := by
  let I : Set SpaceTime := Ioc s t ×ˢ univ
  let C : ℕ → Set SpaceTime := fun n => Icc (s - germWidth n) (t + germWidth n) ×ˢ univ
  let X := supportedNoiseSigma (mΩ := mΩ) P W I
  let H := fun n => supportedNoiseSigma (mΩ := mΩ) P W (C n)
  let O := fun n => supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth n))
  have hH (n : ℕ) : H n ≤ mΩ := supportedNoiseSigma_le (mΩ := mΩ) P hW (C n)
  have hO (n : ℕ) : O n ≤ mΩ :=
    supportedNoiseSigma_le (mΩ := mΩ) P hW (exteriorStrip s t (germWidth n))
  have hXH (n : ℕ) : X ≤ H n := by
    apply supportedNoiseSigma_mono (mΩ := mΩ) P W
    intro z hz
    have hw := germWidth_pos n
    exact ⟨⟨by linarith only [hw, hz.1.1], by linarith only [hw, hz.1.2]⟩, trivial⟩
  have hmono : Monotone O := fun i j hij =>
    supportedNoiseSigma_mono (mΩ := mΩ) P W (exteriorStrip_germ_mono s t hij)
  have hind (n : ℕ) : Indep (H n) (O n) P := by
    apply indep_supportedNoiseSigma (mΩ := mΩ) P hW
    rw [exteriorStrip_eq_compl]
    exact disjoint_compl_right
  have hjoin : H 0 ≤ X ⊔ ⨆ n, O n := by
    have h := supportedNoiseSigma_le_split (mΩ := mΩ) P hW I
      (measurableSet_Ioc.prod MeasurableSet.univ) (C 0)
    rw [← iSup_exteriorNoiseSigma (mΩ := mΩ) P hW s t] at h
    exact h
  have he := independent_complement_descent (mΩ := mΩ) P X H O hH hO hXH hmono hind hjoin
    (null_le_supportedNoiseSigma (mΩ := mΩ) P W I)
  exact he

end GlobalPhi43.Flow
