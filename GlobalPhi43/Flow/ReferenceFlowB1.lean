module

public import GlobalPhi43.Flow.FlowJointParameter
public import GlobalPhi43.Flow.EventFlowRestart
public import GlobalPhi43Statements.Defs.IsContinuousMeasurableFlow

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Joint parameter measurability and the restart identity for the reference flow,
using its window measurability and its restart identity on every outcome. -/
theorem referenceEventFlow_B1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    GlobalPhi43.IsContinuousMeasurableFlow
      (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) (fun t s x ω => u.value ω t s x) := by
  refine ⟨?_, ?_, ?_, ?_, u.b1_restart⟩
  · let D := {p : ℝ × ℝ // 0 ≤ p.2 ∧ p.2 ≤ p.1} × HolderBesov η × Ω
    let f : D → HolderBesov η × ((ℝ × Ici (0 : ℝ)) × Ω) := fun q =>
      (q.2.1, ((q.1.val.1, ⟨q.1.val.2, q.1.property.1⟩), q.2.2))
    have hf : Measurable f := by fun_prop
    have he := (referenceFlow_joint_parameter_measurable P hW N hN κ hκE
      ρ hρ mass η hη hκη ξ hξ u).comp hf
    convert he using 1
    funext q
    dsimp only [f, Function.comp_def]
    rw [max_eq_left q.1.property.2]
  · intro ω hω t s _ _ x
    exact u.value_off hω t s x
  · intro ω s hs
    exact (u.continuous_on ω s hs).comp_continuous
      (continuous_fst.subtype_val.prodMk continuous_snd) (fun p => ⟨p.1.property, mem_univ _⟩)
  · intro s hs x ω
    exact u.initial ω s hs x

end GlobalPhi43.Flow
