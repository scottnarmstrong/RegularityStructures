module

public import GlobalPhi43.Flow.WindowLimitMeasurable
public import GlobalPhi43.Markov.Measurability

public noncomputable section

open MeasureTheory Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The producer's fixed-start continuity gives datum continuity at each endpoint. -/
theorem EventFlow.continuous_datum {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent}
    {E : Set Ω} {a : E → ℕ → LiftData N κ} (u : EventFlow E η a)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Continuous (fun x => u.value ω t s x) :=
  (u.continuous_on ω s hs).comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hst, mem_univ _⟩)

/-- Deterministic smooth approximation in the same closed ball. This is not
an additional random selection, nor a new dense selector on noise sequences. -/
theorem exists_smooth_sequence (η : NegExponent) (x : HolderBesov η) :
    ∃ q : ℕ → C(Torus3, ℝ), (∀ n, IsSmoothOnTorus (q n)) ∧
      Tendsto (fun n => toHolderBesov η (q n)) atTop (𝓝 x) := by
  let z : StateBall η ‖x‖ := ⟨x, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp ((dense_smoothBall η ‖x‖) z)
  refine ⟨fun n => smoothRepresentative ⟨q n, hq n⟩,
    fun n => (smoothRepresentative_spec ⟨q n, hq n⟩).1, ?_⟩
  have ht := continuous_subtype_val.tendsto z |>.comp hlim
  have he : (fun n => toHolderBesov η (smoothRepresentative ⟨q n, hq n⟩)) =
      (fun n => (q n).val) := funext fun n => (smoothRepresentative_spec ⟨q n, hq n⟩).2
  rw [he]
  exact ht

section Reference

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "hsmooth" => (fun ε hε => And.left (hξ ε hε))
local notation "E" => referenceEvent N κ ρ mass η ξ hsmooth
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ hsmooth (Subtype.val ω) (Subtype.property ω))

/-- Exact completed-window measurability of the SAME reference flow for every
rough datum. No endpoint measurability or extra event is an input. -/
theorem referenceFlow_window_measurable (u : EventFlow E η A)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : HolderBesov η) :
    Measurable[noiseWindowSigma P W s t] (fun ω => u.value ω t s x) := by
  obtain ⟨q, hq, hlim⟩ := exists_smooth_sequence η x
  apply @measurable_of_tendsto_metrizable Ω (HolderBesov η)
    (noiseWindowSigma P W s t) _ _ _ _ _ _
    (fun n => referenceFlow_smooth_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη
      ξ hξ u hs hst (q n) (hq n))
  apply tendsto_pi_nhds.mpr
  intro ω
  exact ((u.continuous_datum ω hs hst).tendsto x).comp hlim

/-- Literal fixed-window product measurability, including the identity fallback.
The noise field is fixed only AFTER the deterministic start pair is fixed. -/
theorem referenceFlow_joint_window_measurable (u : EventFlow E η A)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    @Measurable (HolderBesov η × Ω) (HolderBesov η)
      ((inferInstance : MeasurableSpace (HolderBesov η)).prod (noiseWindowSigma P W s t)) inferInstance
      (fun p => u.value p.2 t s p.1) := by
  exact @Markov.measurable_joint_of_sections (HolderBesov η) Ω (HolderBesov η)
    _ _ _ _ (noiseWindowSigma P W s t) _ _ _
    (fun x ω => u.value ω t s x) (fun ω => u.continuous_datum ω hs hst)
    (fun x => referenceFlow_window_measurable P hW N hN κ hκE ρ hρ mass η hη hκη
      ξ hξ u hs hst x)

end Reference
end GlobalPhi43.Flow
