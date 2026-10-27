module

public import GlobalPhi43.Invariant.StationaryInputs
public import GlobalPhi43.Invariant.StationaryReindex
public import GlobalPhi43.Invariant.StationaryFlow
public import GlobalPhi43Statements.Defs.IsKrylovBogoliubovInvariant
public import GlobalPhi43Statements.Defs.IsStationarySolution

/-! # Stationary solutions from a given flow and invariant measure -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Set
open scoped NNReal

namespace GlobalPhi43.Invariant

/-- Joint measurability, the Feller Markov property and invariance imply stationarity.
No additional moment estimate is required once the invariant measure is given. -/
theorem isStationarySolution_of_isKrylovBogoliubovInvariant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {η : NegExponent}
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    {Ω₀ : Set Ω} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (h6 : IsFellerMarkovFlow P W u)
    (μ : Measure (HolderBesov η)) [IsProbabilityMeasure μ]
    (h7 : IsKrylovBogoliubovInvariant P u μ) : IsStationarySolution P W u μ := by
  have hj : Measurable (fun q : (ℝ≥0 × HolderBesov η) × Ω => u q.1.1 0 q.1.2 q.2) := by
    have ht : Measurable (fun q : (ℝ≥0 × HolderBesov η) × Ω =>
        (⟨(q.1.1, 0), le_rfl, q.1.1.property⟩ :
          {r : ℝ × ℝ // 0 ≤ r.2 ∧ r.2 ≤ r.1})) :=
      ((measurable_fst.fst.subtype_val).prodMk measurable_const).subtype_mk
    exact hu.1.comp (ht.prodMk (measurable_fst.snd.prodMk measurable_snd))
  let ν : ProbabilityMeasure (HolderBesov η) := ⟨μ, inferInstance⟩
  have hi (s : ℝ≥0) : Markov.flowObservationKernel P u hj s ∘ₘ μ = μ := by
    ext A hA
    rw [Measure.bind_apply hA (Markov.flowObservationKernel P u hj s).aemeasurable]
    exact h7.1 s s.property A hA
  let m (s : ℝ≥0) := noiseWindowSigma P W 0 s
  have hm (s : ℝ≥0) : m s ≤ (inferInstance : MeasurableSpace Ω) := Markov.noiseWindowSigma_le P hW 0 s
  have hmono : Monotone m := fun s t hst => Markov.noiseWindowSigma_mono P W le_rfl
    (show (s : ℝ) ≤ t from hst)
  have ha (s : ℝ≥0) (x : HolderBesov η) : Measurable[m s] (u s 0 x) :=
    measurable_flow_noiseWindowSigma P W hW u hu h6 s x
  have hz (x : HolderBesov η) : u 0 0 x =ᵐ[P] fun _ => x :=
    ae_of_all P (fun ω => hu.2.2.2.1 0 le_rfl x ω)
  have hc (s t : ℝ≥0) (hst : s ≤ t) (x : HolderBesov η) (g : HolderBesov η → ℝ)
      (hg : Measurable g) (hb : ∀ y, ‖g y‖ ≤ 1) :
      P[fun ω => g (u t 0 x ω) | m s] =ᵐ[P]
        fun ω => flowTransition P u (t - s : ℝ≥0) g (u s 0 x ω) := by
    have he := h6.2.2.2.2.1 g hg ⟨1, fun y => by simpa only [Real.norm_eq_abs] using hb y⟩
      s (t - s : ℝ≥0) s.property (NNReal.coe_nonneg _) x
    have heq : (s : ℝ) + (t - s : ℝ≥0) = t := by rw [NNReal.coe_sub hst]; ring
    simpa only [heq] using he
  obtain ⟨hw, hinit, _, _, hone, hord⟩ :=
    stationary_flow_product P W hW u hj ν hi m hm hmono ha hz hc
  have hs (t : ℝ≥0) : Measurable (fun q : Ω × HolderBesov η => u t 0 q.2 q.1) :=
    hj.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  refine ⟨?_, ?_, hw, hinit, noise_initial_indep_product P μ W hW⟩
  · intro k t ht r hr
    exact stationary_real_tuples (P.prod μ) (fun t q => u t 0 q.2 q.1) hs hord k t ht r hr
  · intro t ht
    exact hone ⟨t, ht⟩

end GlobalPhi43.Invariant
