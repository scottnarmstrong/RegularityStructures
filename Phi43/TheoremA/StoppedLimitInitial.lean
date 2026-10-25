/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.StoppedLimitMeasurable

/-!
# Initial value of the stopped limit

If every approximating path starts at the same continuous function, the stopped pointwise limit
has that initial value whenever its lifetime is positive.
-/

public section

open Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyStoppedLimit_initial
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (τ : Ω → ℝ≥0∞)
    (x₀ : HolderBesov η)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t))
    (hinitial : ∀ n ω, x n ω 0 = x₀)
    (hτpos : ∀ ω, 0 < τ ω) :
    ∀ ω, assemblyStoppedLimit x τ hCauchy ω 0 = x₀ := by
  intro ω
  have h0 : ENNReal.ofReal (0 : ℝ) < τ ω := by
    simpa using hτpos ω
  have hvalue : assemblyStoppedLimit x τ hCauchy ω 0 =
      Classical.choose (cauchySeq_tendsto_of_complete (hCauchy ω 0 (by positivity) h0)) := by
    dsimp [assemblyStoppedLimit]
    split
    · rfl
    · rename_i h
      exact False.elim (h ⟨by positivity, h0⟩)
  have hlim := Classical.choose_spec
    (cauchySeq_tendsto_of_complete (hCauchy ω 0 (by positivity) h0))
  have hlim' : Tendsto (fun _ : ℕ => x₀) atTop
      (𝓝 (Classical.choose (cauchySeq_tendsto_of_complete
        (hCauchy ω 0 (by positivity) h0)))) := by
    exact hlim.congr' (Eventually.of_forall fun n => hinitial n ω)
  have heq : x₀ = Classical.choose (cauchySeq_tendsto_of_complete
      (hCauchy ω 0 (by positivity) h0)) :=
    tendsto_nhds_unique tendsto_const_nhds hlim'
  exact hvalue.trans heq.symm

end RegularityStructures.Phi43

end
