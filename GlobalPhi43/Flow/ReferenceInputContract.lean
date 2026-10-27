module

public import GlobalPhi43.Flow.TranslatedInputs
public import GlobalPhi43.Flow.CompatibleFiniteLimits

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- A later-state bound with radius chosen after the persistence time and before
all indices, starts and smooth data. This predicate assumes the bound; it does not
assert an analytic majorant. -/
@[expose] def LaterStateSupplier {N : ℕ} {κ : Kappa} (η : NegExponent)
    (A : ℕ → LiftData N κ) : Prop :=
  ∀ S T L h₀ : ℝ, 0 ≤ S → 1 ≤ T → 1 ≤ L → 0 < h₀ → h₀ ≤ 1 →
    ∃ R : ℝ, 1 ≤ R ∧ ∀ n (s : Icc (0 : ℝ) S), LaterStateBound η L T h₀ R (A n) s.val

/-- For the same reference event and dyadic family, the finite analytic inputs
are equivalent to the later-state bounds: the horizon bounds follow from the
reference-family estimates. No limit, solution Cauchy estimate, additional event or
size allowance is assumed. -/
theorem reference_finiteInputs_iff_later {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (mass : ℝ) (η : NegExponent)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ mass η ξ hsmooth) :
    let A := dyadicLiftData N κ ρ mass η ξ hsmooth ω hω
    FiniteAnalyticInputs η A ↔ LaterStateSupplier η A := by
  dsimp only
  constructor
  · intro inputs
    exact inputs.later
  · intro hlater
    refine ⟨?_, hlater⟩
    intro S T hS hT
    obtain ⟨B, hB, hsize, hC, _, _, _⟩ :=
      reference_translated_inputs N κ ρ mass η ξ hsmooth ω hω S T hS hT
    exact ⟨B, hB, hsize, hC⟩

end GlobalPhi43.Flow
