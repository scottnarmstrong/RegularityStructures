module

public import GlobalPhi43.Flow.HomogeneityConsumer
public import GlobalPhi43.Flow.DyadicLiftData
public import GlobalPhi43Statements.Defs.IsTimeHomogeneous
import Mathlib.Tactic.Ring

/-! Time homogeneity for a specified reference flow. No event, drift-binding or forcing-binding premise is added. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Homogeneity of any supplied producer for the exact reference event and dyadic family.
The theorem does not construct that producer or discharge its physical majorant. -/
theorem referenceEventFlow_homogeneous_law {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.val ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.val < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow
      (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    (s : ℝ) (hs : 0 ≤ s) (T : I → ℝ) (hT : ∀ i, 0 ≤ T i) (x : I → HolderBesov η) :
    IdentDistrib (fun ω i => u.value ω (s + T i) s (x i))
      (fun ω i => u.value ω (T i) 0 (x i)) P P := by
  have hε (n : ℕ) : dyadicTailScale n ∈ Ioc (0 : ℝ) 1 := by
    change (2⁻¹ : ℝ) ^ (n + 1) ∈ Ioc (0 : ℝ) 1
    exact ⟨pow_pos (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have he := referenceEvent_measurable_measure_one P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
  have hE : ∀ᵐ ω ∂P, ω ∈ referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) :=
    ae_iff.mpr ((prob_compl_eq_zero_iff he.1).mpr he.2)
  apply eventFlow_homogeneous_law hW hρ (fun n => (hε n).1)
    (fun n => hξ _ (hε n)) u hE
    (fun n => mass + 3 * wickConstant ρ (dyadicTailScale n) - 9 * sunsetConstant ρ (dyadicTailScale n))
    (fun _ _ => rfl) ?_ s hs T hT x
  intro ω
  funext n
  dsimp only [liftDriftSequence, dyadicLiftData]
  ring

/-- Time homogeneity for the same specified reference flow, in the standard argument order. -/
theorem referenceEventFlow_isTimeHomogeneous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.val ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.val < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow
      (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    : GlobalPhi43.IsTimeHomogeneous P (fun t s x ω => u.value ω t s x) := by
  intro s hs k _ T hT x
  exact (referenceEventFlow_homogeneous_law P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
    u s hs T hT x).map_eq

end GlobalPhi43.Flow
