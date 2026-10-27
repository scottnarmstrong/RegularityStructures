module

public import GlobalPhi43.Compactness.Embedding
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Layercake

/-! # Lower-semicontinuous Portmanteau, including infinite values -/

public noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The layer-cake proof of Portmanteau for a nonnegative real lsc function.
Continuity is not required: only its strict superlevel sets must be open. -/
theorem lintegral_le_liminf_of_open_sets_real {μ : Measure E} {μs : ℕ → Measure E}
    {f : E → ℝ} (hf : LowerSemicontinuous f) (hn : ∀ x, 0 ≤ f x)
    (hop : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun n => μs n G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂μs n) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hn) hf.measurable.aemeasurable]
  exact (lintegral_mono (fun r => hop _ (hf.isOpen_preimage r))).trans
    (lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
      measure_mono (fun x hx => lt_of_le_of_lt hst hx))))

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Finite truncation preserves lower semicontinuity after passing to real values. -/
theorem lowerSemicontinuous_truncate {g : E → ℝ≥0∞} (hg : LowerSemicontinuous g)
    (n : ℕ) : LowerSemicontinuous (fun x => (min (g x) (n : ℝ≥0∞)).toReal) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro r
  change IsOpen {x | r < (min (g x) (n : ℝ≥0∞)).toReal}
  by_cases hr : r < 0
  · have he : {x | r < (min (g x) (n : ℝ≥0∞)).toReal} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hr.trans_le ENNReal.toReal_nonneg
    rw [he]
    exact isOpen_univ
  · have he : {x | r < (min (g x) (n : ℝ≥0∞)).toReal} =
        {x | ENNReal.ofReal r < g x} ∩ {x : E | ENNReal.ofReal r < (n : ℝ≥0∞)} := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff]
      rw [← ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hr)
        (ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by finiteness))), lt_min_iff]
    rw [he]
    exact (hg.isOpen_preimage _).inter isOpen_const

/-- Extended-valued lsc Portmanteau from the open-set inequalities.
The finite truncations increase to g, so no finiteness assumption is imposed. -/
theorem lintegral_le_liminf_of_open_sets {μ : Measure E} {μs : ℕ → Measure E}
    {g : E → ℝ≥0∞} (hg : LowerSemicontinuous g)
    (hop : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun n => μs n G)) :
    ∫⁻ x, g x ∂μ ≤ atTop.liminf (fun n => ∫⁻ x, g x ∂μs n) := by
  have hsup (x : E) : (⨆ n : ℕ, min (g x) (n : ℝ≥0∞)) = g x := by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  calc
    ∫⁻ x, g x ∂μ = ∫⁻ x, ⨆ n : ℕ, min (g x) (n : ℝ≥0∞) ∂μ := by
      simp only [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, min (g x) (n : ℝ≥0∞) ∂μ :=
      lintegral_iSup (fun n => hg.measurable.min measurable_const)
        (fun n m hnm x => min_le_min_left _ (by exact_mod_cast hnm))
    _ ≤ atTop.liminf (fun n => ∫⁻ x, g x ∂μs n) := by
      refine iSup_le fun n => ?_
      have h := lintegral_le_liminf_of_open_sets_real
        (lowerSemicontinuous_truncate hg n) (fun _ => ENNReal.toReal_nonneg) hop
      simp only [ENNReal.ofReal_toReal (ne_of_lt
        (lt_of_le_of_lt (min_le_right _ _) (by finiteness)))] at h
      exact h.trans (Filter.liminf_le_liminf (Eventually.of_forall fun k =>
        lintegral_mono fun x => min_le_left _ _))

variable [PolishSpace E]

/-- Weakly convergent Borel probabilities satisfy Portmanteau for every nonnegative
extended-valued lower-semicontinuous function. -/
theorem lintegral_le_liminf_of_tendsto {μ : ProbabilityMeasure E}
    {μs : ℕ → ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ))
    {g : E → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    ∫⁻ x, g x ∂(μ : Measure E) ≤
      atTop.liminf (fun n => ∫⁻ x, g x ∂(μs n : Measure E)) :=
  lintegral_le_liminf_of_open_sets hg (fun _ hG =>
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG)

end GlobalPhi43.Invariant
