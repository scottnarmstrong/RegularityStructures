module

public import GlobalPhi43.Flow.ReferenceFlowB1
public import GlobalPhi43.Flow.ReferenceHomogeneity
public import GlobalPhi43.Markov.FlowMarkov
public import GlobalPhi43Statements.Defs.IsWindowAdapted

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43

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

/-- Window adaptation on the fixed event, without an intersection over real starts. -/
theorem referenceEventFlow_B2 (u : EventFlow E η A) :
    GlobalPhi43.IsWindowAdapted P W (fun t s x ω => u.value ω t s x) := by
  intro s t hs hst x
  exact referenceFlow_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u hs hst x

/-- Joint time/data/noise samples of the same producer, in sampled-kernel order. -/
theorem referenceFlow_samples_measurable (u : EventFlow E η A) :
    Measurable (fun p : (Ici (0 : ℝ) × HolderBesov η) × Ω =>
      u.value p.2 p.1.1.val 0 p.1.2) := by
  let f : (Ici (0 : ℝ) × HolderBesov η) × Ω →
      HolderBesov η × ((ℝ × Ici (0 : ℝ)) × Ω) := fun p =>
    (p.1.2, ((p.1.1.val, ⟨0, le_rfl⟩), p.2))
  have hf : Measurable f := by fun_prop
  have he := (referenceFlow_joint_parameter_measurable P hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ u).comp hf
  convert he using 1
  funext p
  dsimp only [f, Function.comp_def]
  rw [max_eq_left p.1.1.property]

theorem referenceFlow_sample_measurable (u : EventFlow E η A) (t : ℝ) (ht : 0 ≤ t)
    (x : HolderBesov η) : Measurable (fun ω => u.value ω t 0 x) := by
  exact (referenceFlow_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
    u le_rfl ht x).mono (Markov.noiseWindowSigma_le P hW 0 t) le_rfl

/-- Joint datum/noise measurability at a fixed nonnegative time. -/
theorem referenceFlow_state_noise_measurable (u : EventFlow E η A) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun p : HolderBesov η × Ω => u.value p.2 t 0 p.1) := by
  let f : HolderBesov η × Ω → HolderBesov η × ((ℝ × Ici (0 : ℝ)) × Ω) :=
    fun p => (p.1, ((t, ⟨0, le_rfl⟩), p.2))
  have hf : Measurable f := by fun_prop
  have he := (referenceFlow_joint_parameter_measurable P hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ u).comp hf
  convert he using 1
  funext p
  dsimp only [f, Function.comp_def]
  rw [max_eq_left ht]

/-- The future-window law is derived from the actual reference homogeneity
application, not supplied as a conditional-law premise. -/
theorem referenceFlow_future_law (u : EventFlow E η A) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : HolderBesov η) :
    P.map (fun ω => u.value ω (s + t) s x) =
      flowLaw P (fun t s x ω => u.value ω t s x) t x := by
  have he := referenceEventFlow_homogeneous_law (I := Unit) P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ u s hs (fun _ => t) (fun _ => ht) (fun _ => x)
  exact (he.comp (measurable_pi_apply ())).map_eq

/-- Conditional Markov identity: every input to the generic restart
theorem follows from the reference causality, law and restart identities.
Future/past independence is the actual white-noise window theorem. -/
theorem referenceFlow_condExp (u : EventFlow E η A) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : HolderBesov η) {f : HolderBesov η → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ y, |f y| ≤ C) :
    P[fun ω => f (u.value ω (s + t) 0 x) | noiseWindowSigma P W 0 s] =ᵐ[P]
      fun ω => flowTransition P (fun t s x ω => u.value ω t s x) t f (u.value ω s 0 x) := by
  apply Markov.flowTransition_condExp_of_restart (u := fun t s x ω => u.value ω t s x)
    hW s t x
    (referenceFlow_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u le_rfl hs x)
    (referenceFlow_joint_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
      u hs (le_add_of_nonneg_right ht))
    (fun y => referenceFlow_future_law P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u s t hs ht y)
    (ae_of_all _ (fun ω => (u.cocycle ω 0 s (s + t) le_rfl hs (le_add_of_nonneg_right ht) x).symm))
    hf hb

end Reference
end GlobalPhi43.Flow
