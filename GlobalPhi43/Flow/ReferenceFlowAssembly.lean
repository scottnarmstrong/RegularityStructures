module

public import GlobalPhi43.Flow.ReferenceInputContract
public import GlobalPhi43.Flow.MajorantLaterState
public import GlobalPhi43.Flow.EventFlow

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The every-start majorant implies the finite analytic inputs. The persistence
time is selected before the later-state radius. -/
theorem reference_finiteInputs_of_majorant {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (mass : ℝ) (η : NegExponent)
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (c : ℝ) (hc : 0 ≤ c)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ mass η ξ hsmooth)
    (hmajorant : EveryStartMajorant c (dyadicLiftData N κ ρ mass η ξ hsmooth ω hω)) :
    FiniteAnalyticInputs η (dyadicLiftData N κ ρ mass η ξ hsmooth ω hω) := by
  apply (reference_finiteInputs_iff_later N κ ρ mass η ξ hsmooth ω hω).mpr
  intro S T L h₀ hS hT _ hh₀ hh₀1
  obtain ⟨R, hR, hbound⟩ := reference_laterStateBound N κ ρ mass η hκη c hc
    ξ hsmooth ω hω hmajorant S T L h₀ hS hT hh₀ hh₀1
  exact ⟨R, hR, fun n s => hbound n s.val s.property⟩

/-- One all-horizon flow on the exact reference event and family.
All solution estimates and limits are constructed, not supplied. Only the
literal every-start majorant remains an analytic premise. The off-event
value and all finite-limit properties are those of the existing EventFlow. -/
theorem exists_referenceEventFlow {Ω : Type*} (N : ℕ) (hN : 5 ≤ N)
    (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (mass : ℝ) (η : NegExponent)
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (c : ℝ) (hc : 0 ≤ c)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (hmajorant : ∀ ω : referenceEvent N κ ρ mass η ξ hsmooth,
      EveryStartMajorant c (dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property)) :
    Nonempty (EventFlow (referenceEvent N κ ρ mass η ξ hsmooth) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property)) := by
  apply exists_eventFlow hκE hN hη hκη
  intro ω
  exact reference_finiteInputs_of_majorant N κ ρ mass η hκη c hc ξ hsmooth
    ω.val ω.property (hmajorant ω)

end GlobalPhi43.Flow
