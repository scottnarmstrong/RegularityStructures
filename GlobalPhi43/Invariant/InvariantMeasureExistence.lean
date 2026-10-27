module

public import GlobalPhi43.Invariant.FlowKernel
public import GlobalPhi43.Invariant.MomentAssembly
public import GlobalPhi43.Assembly.StrongerLate
public import GlobalPhi43Statements.Defs.IsKrylovBogoliubovInvariant

/-! # An invariant law of a given flow with quantitative moments -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

/-- Quantitative invariant-measure existence for a given Feller Markov flow.
The profile precedes the noise space; one selected measure supports every
stronger exponent and real moment. -/
theorem exists_invariantMeasure (C : ℝ → ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {η : NegExponent} (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (W : (SpaceTime → ℝ) → Ω → ℝ) {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (h6 : IsFellerMarkovFlow P W u)
    (hstrong : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω, Assembly.strongWindowSup α u r ω ^ p ∂P) ≤ C α p) :
    ∃ μ : ProbabilityMeasure (HolderBesov η),
      IsKrylovBogoliubovInvariant P u (μ : Measure _) ∧
      ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
        ∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _) ≤ C α p := by
  let ρ := Assembly.flowOrbitKernel P u hu (0 : HolderBesov η)
  have hlate := Assembly.flowOrbit_late_moments C P u hu (0 : HolderBesov η) hstrong
  have horbit (t : ℝ) (ht : 0 ≤ t) : ρ t = flowKernel h6 ⟨t, ht⟩ 0 :=
    Assembly.flowOrbitKernel_apply P u hu 0 ht
  obtain ⟨μ, T, hT, hTlim, ⟨ν, hν, hνlim⟩, hinv, hmom⟩ :=
    exists_invariant_with_moments η hη (flowKernel h6)
      (flowKernel_feller h6) ρ 0 horbit (flowKernel_semigroup h6)
      (fun α p => (C α p : ℝ≥0∞)) (fun _ _ _ _ _ => ENNReal.coe_ne_top) hlate
  have he : ρ = nonnegativeLawKernel (fun t : Ici (0 : ℝ) => flowLaw P u t 0)
      (measurable_flowLaw_orbit h6 0) := rfl
  have havg (t : ℝ) : fullAverage ρ t = averagedLaw P u t := by
    rw [averagedLaw_eq_fullAverage P u (measurable_flowLaw_orbit h6 0), he]
  refine ⟨μ, ⟨?_, ⟨T, fun n => zero_lt_one.trans (hT n), hTlim, ?_⟩, ?_⟩, ?_⟩
  · intro t ht A hA
    have hi := congrArg (fun m : Measure (HolderBesov η) => m A) (hinv ⟨t, ht⟩)
    rw [Measure.bind_apply hA (flowKernel h6 ⟨t, ht⟩).aemeasurable] at hi
    exact hi
  · intro f
    have hi := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hνlim f
    simpa only [hν, havg] using hi
  · intro p hp α hα hα'
    exact (hmom α hα hα' p hp).2
  · intro α hα hα' p hp
    exact (hmom α hα hα' p hp).1

end GlobalPhi43.Invariant
