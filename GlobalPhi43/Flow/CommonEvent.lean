module

public import GlobalPhi43.Flow.WindowEvent
public import Phi43.Steps.GModelsConvergence

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

variable {Ω : Type*} {κ : Kappa}

/-- The dyadic convergence event of Theorem A, clause (iii). -/
def modelConvergenceEvent (α : ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) : Set Ω :=
  {ω | ∀ T : ℕ, 1 ≤ T →
    (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
      Statements.phi43Dist κ α T (Z ((2 : ℝ) ^ n)⁻¹ ω) (Z ((2 : ℝ) ^ m)⁻¹ ω)
        (ψ ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ m)⁻¹ ω) ≤ ENNReal.ofReal δ) ∧
    ∃ B : ℝ, ∀ n : ℕ,
      Statements.phi43Size κ α T (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤
        ENNReal.ofReal B}

/-- The n-th canonical-bound event: exact noise growth and the actual model/potential lift
specification, with the prescribed renormalisation constants. -/
def canonicalBoundEvent (N : ℕ) (ρ : ParabolicSpace → ℝ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) (n : ℕ) : Set Ω :=
  Attachment.growthEvent (ξ ((2⁻¹ : ℝ) ^ n)) ∩
    {ω | Statements.IsModeratePhi43Lift N κ (ξ ((2⁻¹ : ℝ) ^ n) ω)
      (wickConstant ρ ((2⁻¹ : ℝ) ^ n) + a / 3,
        sunsetConstant ρ ((2⁻¹ : ℝ) ^ n) + 0)
      (Z ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ n) ω)}

/-- The stipulated intersection of canonical-bound events, retaining n ≥ 1. -/
def dyadicCanonicalEvent (N : ℕ) (ρ : ParabolicSpace → ℝ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) : Set Ω :=
  ⋂ n : ℕ, ⋂ (_ : 1 ≤ n), canonicalBoundEvent N ρ a ξ Z ψ n

/-- Literal Ω₀^α. It is chosen before, and does not quantify over, real start times. -/
def commonEvent (N : ℕ) (ρ : ParabolicSpace → ℝ) (a α : ℝ) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) : Set Ω :=
  (modelConvergenceEvent α Z ψ ∩ dyadicCanonicalEvent N ρ a ξ Z ψ) ∩ windowEvent (lossExponent κ) Z ψ

/-- Every member of the literal common event has the actual canonical and potential bounds
at every stipulated dyadic index, not just an almost-sure specification. -/
theorem commonEvent_lift (N : ℕ) (ρ : ParabolicSpace → ℝ) (a α : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) {ω : Ω}
    (hω : ω ∈ commonEvent N ρ a α ξ Z ψ) (n : ℕ) (hn : 1 ≤ n) :
    Statements.IsModeratePhi43Lift N κ (ξ ((2⁻¹ : ℝ) ^ n) ω)
      (wickConstant ρ ((2⁻¹ : ℝ) ^ n) + a / 3,
        sunsetConstant ρ ((2⁻¹ : ℝ) ^ n) + 0)
      (Z ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ n) ω) :=
  (mem_iInter.mp (mem_iInter.mp hω.1.2 n) hn).2


universe u

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
  (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
  (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ))
  (hlift : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
    Statements.IsModeratePhi43Lift N κ (ξ ε ω)
      (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0) (Z ε ω) (ψ ε ω))

include hlift in
/-- Simultaneous canonical and potential bounds for all n ≥ 1 on the literal intersection. -/
theorem dyadicCanonicalEvent_measurable_measure_one [P.IsComplete] :
    MeasurableSet (dyadicCanonicalEvent N ρ a ξ Z ψ) ∧
      P (dyadicCanonicalEvent N ρ a ξ Z ψ) = 1 := by
  have hn (n : ℕ) : ∀ᵐ ω ∂P, ω ∈ canonicalBoundEvent N ρ a ξ Z ψ n := by
    have h := hlift ((2⁻¹ : ℝ) ^ n)
      ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
    exact h.mono fun _ hω => ⟨hω.1, hω⟩
  apply measurableSet_measure_one_of_ae P
  filter_upwards [ae_all_iff.2 hn] with ω hω
  exact mem_iInter.2 fun n => mem_iInter.2 fun _ => hω n

include W hW ρ hρ hξ

include hκE N hN a Z ψ hlift

/-- The common event combining dyadic convergence, canonical bounds and window bounds. -/
theorem commonEvent_measurable_measure_one [P.IsComplete]
    (α : NegExponent) (hα : (α : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκα : κ.1 < -(1 / 2 : ℝ) - α) :
    MeasurableSet (commonEvent N ρ a α ξ Z ψ) ∧ P (commonEvent N ρ a α ξ Z ψ) = 1 := by
  have hG := (phi43GModels_convergence κ hκE N hN α hα hκα ρ ρ hρ hρ (a / 3, 0)
    P W hW ξ ξ hξ hξ Z Z ψ ψ hlift hlift).2.2
  have hcanonical := dyadicCanonicalEvent_measurable_measure_one P κ N ρ a ξ Z ψ hlift
  have hgr : ∀ᵐ ω ∂P, ω ∈ dyadicCanonicalEvent N ρ a ξ Z ψ :=
    (mem_ae_iff_prob_eq_one hcanonical.1).mpr hcanonical.2
  have hwin := ae_window_events P W hW κ hκE N hN ρ hρ a ξ hξ Z ψ hlift
  apply measurableSet_measure_one_of_ae P
  filter_upwards [hG, hgr, hwin] with ω hω hgrω hwinω
  exact ⟨⟨hω, hgrω⟩, hwinω.1⟩

end GlobalPhi43.Flow
