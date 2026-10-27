module

public import GlobalPhi43.Flow.ReferenceFlowB135
public import GlobalPhi43.Flow.ReferenceFlowB6
public import GlobalPhi43.Assembly.GlobalInvariantAssembly

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

section Reference

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "E" => referenceEvent N κ ρ mass η ξ (fun ε hε => And.left (hξ ε hε))
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ
  (fun ε hε => And.left (hξ ε hε)) (Subtype.val ω) (Subtype.property ω))

/-- An invariant law and stationary solution for a specified reference flow.
The event, joint measurability, restart, adaptation, regularisation convergence,
time homogeneity and Markov property follow from the noise data. The coming-down
estimate and stronger moment bounds are the additional analytic assumptions. -/
theorem referenceEventFlow_global_of_moments (K : ℝ → ℝ≥0) (C : ℝ → ℝ → ℝ≥0)
    (u : EventFlow E η A)
    (h4 : ComesDownFromInfinity P K (fun t s x ω => u.value ω t s x))
    (hstrong : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω,
        Assembly.strongWindowSup α (fun t s x ω => u.value ω t s x) r ω ^ p ∂P) ≤ C α p) :
    ∃ μ : ProbabilityMeasure (HolderBesov η),
      IsGlobalPhi43Flow K P W mass η E (fun t s x ω => u.value ω t s x) (μ : Measure _) ∧
      ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
        ∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _) ≤ C α p := by
  obtain ⟨hE, hfull⟩ := referenceEvent_measurable_measure_one P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ
  exact Assembly.exists_global_of_moments K C P hη.2 W hW mass E hE hfull
    (fun t s x ω => u.value ω t s x)
    (referenceEventFlow_B1 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u)
    (referenceEventFlow_B2 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u)
    (referenceEventFlow_B3 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u) h4
    (referenceEventFlow_isTimeHomogeneous P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u)
    (referenceEventFlow_B6 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u) hstrong

end Reference
end GlobalPhi43.Flow
