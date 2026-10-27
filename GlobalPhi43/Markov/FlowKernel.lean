module

public import GlobalPhi43.Markov.Feller
public import GlobalPhi43Statements.Defs.FlowTransition

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open RegularityStructures
open scoped BoundedContinuousFunction

namespace GlobalPhi43.Markov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {η : NegExponent} {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}

/-- A measurable sample gives a probability law. -/
theorem flowLaw_isProbabilityMeasure {t : ℝ} {x : HolderBesov η}
    (hu : Measurable (u t 0 x)) : IsProbabilityMeasure (flowLaw P u t x) :=
  (Measure.isProbabilityMeasure_map_iff hu.aemeasurable).mpr inferInstance

/-- The time-zero identity gives the Dirac law. -/
theorem flowLaw_zero_eq_dirac (x : HolderBesov η) (hzero : ∀ ω, u 0 0 x ω = x) :
    flowLaw P u 0 x = Measure.dirac x := by
  simp only [flowLaw, hzero, Measure.map_const, measure_univ, one_smul]

/-- Parameter-measurable samples give measurable laws. -/
theorem measurable_flowLaw_of_joint
    (hu : Measurable (fun q : (Ici (0 : ℝ) × HolderBesov η) × Ω => u q.1.1 0 q.1.2 q.2))
    {A : Set (HolderBesov η)} (hA : MeasurableSet A) :
    Measurable (fun p : Ici (0 : ℝ) × HolderBesov η => flowLaw P u p.1 p.2 A) :=
  measurable_sampleKernel_apply P _ hu hA

omit [IsProbabilityMeasure P] in
/-- The transition action is the sampled expectation. -/
theorem flowTransition_eq_expectation {t : ℝ} {x : HolderBesov η}
    (hu : Measurable (u t 0 x)) {f : HolderBesov η → ℝ} (hf : Measurable f) :
    flowTransition P u t f x = ∫ ω, f (u t 0 x ω) ∂P := by
  exact integral_map hu.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable

/-- Initial-data continuity and measurable samples imply the Feller property of the transition action. -/
theorem continuous_flowTransition_of_samples {t : ℝ}
    (hm : ∀ x, Measurable (u t 0 x))
    (hc : ∀ᵐ ω ∂P, Continuous (fun x => u t 0 x ω)) (f : HolderBesov η →ᵇ ℝ) :
    Continuous (flowTransition P u t f) := by
  have he : flowTransition P u t f = fun x => ∫ ω, f (u t 0 x ω) ∂P := by
    funext x
    exact flowTransition_eq_expectation (hm x) f.continuous.measurable
  rw [he]
  exact continuous_sample_expectation hm hc f

/-- The uniform bound on the transition action, independent of initial datum. -/
theorem abs_flowTransition_le {t : ℝ} (hm : ∀ x, Measurable (u t 0 x))
    (f : HolderBesov η →ᵇ ℝ) (x : HolderBesov η) : |flowTransition P u t f x| ≤ ‖f‖ := by
  rw [flowTransition_eq_expectation (hm x) f.continuous.measurable]
  exact abs_sample_expectation_le (P := P) (u t 0) f x

/-- Time continuity on the nonnegative time carrier, under the stated path-continuity premise. -/
theorem continuous_time_flowTransition_of_samples (x : HolderBesov η)
    (hm : ∀ t : Ici (0 : ℝ), Measurable (u t 0 x))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t : Ici (0 : ℝ) => u t 0 x ω)) (f : HolderBesov η →ᵇ ℝ) :
    Continuous (fun t : Ici (0 : ℝ) => flowTransition P u t f x) := by
  have he : (fun t : Ici (0 : ℝ) => flowTransition P u t f x) =
      fun t : Ici (0 : ℝ) => ∫ ω, f (u t 0 x ω) ∂P := by
    funext t
    exact flowTransition_eq_expectation (hm t) f.continuous.measurable
  rw [he]
  exact continuous_sample_expectation hm hc f

end GlobalPhi43.Markov
