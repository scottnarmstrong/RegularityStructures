module

public import GlobalPhi43.MW20.KernelTestedIncrement
public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-! Compact-measure integration steps for the MW20 reconstruction.
These justify every convolution and subtraction for continuous local germ
sections, without assuming global boundedness of the smooth source fields. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Continuity of a parametric test against a genuinely compactly concentrated
finite measure. Reuses Mathlib's compact parametric integral theorem. -/
theorem continuous_compact_measure_integral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (ν : Measure ParabolicSpace) [IsFiniteMeasure ν] (q : ℝ)
    (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (G : X × ParabolicSpace → ℝ) (hG : Continuous G) :
    Continuous (fun p => ∫ w, G (p, w) ∂ν) := by
  have hs : ν.restrict (Metric.closedBall 0 q) = ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    simpa only [Metric.mem_closedBall, dist_zero_right] using hν
  have hc := continuous_parametric_integral_of_continuous (μ := ν)
    (f := fun p w => G (p, w)) hG (isCompact_closedBall (0 : ParabolicSpace) q)
  simpa only [hs] using hc

/-- Continuous local sections are integrable against a compact kernel. -/
theorem compact_past_section_integrable (ν : Measure ParabolicSpace) [IsFiniteMeasure ν]
    (q : ℝ) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (f : ParabolicSpace → ℝ)
    (hf : Continuous f) (x : ParabolicSpace) : Integrable (fun w => f (x + w)) ν := by
  apply integrable_of_continuous_compact_ae ν (Metric.closedBall 0 q) (isCompact_closedBall _ _)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hν)
  exact hf.comp (continuous_const.add continuous_id)

/-- Continuity in both the germ base and the test centre. -/
theorem compact_measure_germ_test_continuous
    (ν : Measure ParabolicSpace) [IsFiniteMeasure ν] (q : ℝ)
    (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) :
    Continuous (fun p : ParabolicSpace × ParabolicSpace => pastSmooth ν (fun y => F (p.1, y)) p.2) := by
  have hc : Continuous (fun p : (ParabolicSpace × ParabolicSpace) × ParabolicSpace =>
      F (p.1.1, p.1.2 + p.2)) := by apply hF.comp; fun_prop
  simpa only [pastSmooth] using continuous_compact_measure_integral ν q hν _ hc

/-- Continuous smoothing of a continuous field against a compact measure. -/
theorem compact_measure_pastSmooth_continuous
    (ν : Measure ParabolicSpace) [IsFiniteMeasure ν] (q : ℝ)
    (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (f : ParabolicSpace → ℝ) (hf : Continuous f) :
    Continuous (pastSmooth ν f) := by
  change Continuous (fun x => pastSmooth ν f x)
  have hc : Continuous (fun p : ParabolicSpace × ParabolicSpace => f (p.1 + p.2)) :=
    hf.comp (continuous_fst.add continuous_snd)
  simpa only [pastSmooth] using continuous_compact_measure_integral ν q hν _ hc

/-- Continuity of the tested germ on its actual diagonal. -/
theorem compact_measure_diagonal_test_continuous
    (ν : Measure ParabolicSpace) [IsFiniteMeasure ν] (q : ℝ)
    (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) :
    Continuous (fun x => pastSmooth ν (fun y => F (x, y)) x) := by
  have hc := (compact_measure_germ_test_continuous ν q hν F hF).comp
    (continuous_id.prodMk continuous_id)
  simpa only [Function.comp_def, id_eq] using hc

/-- Continuity of the exact coherence test in the two source base points. -/
theorem compact_measure_germ_increment_continuous
    (ν : Measure ParabolicSpace) [IsFiniteMeasure ν] (q : ℝ)
    (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q) (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) :
    Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      pastSmooth ν (fun y => F (p.1, y) - F (p.2, y)) p.2) := by
  have hc : Continuous (fun p : (ParabolicSpace × ParabolicSpace) × ParabolicSpace =>
      F (p.1.1, p.1.2 + p.2) - F (p.1.2, p.1.2 + p.2)) := by
    apply Continuous.sub <;> apply hF.comp <;> fun_prop
  simpa only [pastSmooth] using continuous_compact_measure_integral ν q hν _ hc

/-- Exact convolution testing for any integrable field section. In the source
application integrability is derived from smoothness and actual support. -/
theorem pastSmooth_conv_of_integrable
    (σ ν : Measure ParabolicSpace) [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hi : Integrable (fun z => f (x + z)) (σ.conv ν)) :
    pastSmooth (σ.conv ν) f x = pastSmooth σ (pastSmooth ν f) x := by
  unfold pastSmooth
  rw [integral_conv hi]
  simp only [add_assoc]

/-- Literal subtraction of two compact-kernel tests, with the exact
integrability obligations exposed for use by the source proof. -/
theorem pastSmooth_sub_of_integrable (ν : Measure ParabolicSpace)
    (f g : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hf : Integrable (fun z => f (x + z)) ν) (hg : Integrable (fun z => g (x + z)) ν) :
    pastSmooth ν (fun y => f y - g y) x = pastSmooth ν f x - pastSmooth ν g x :=
  integral_sub hf hg

end GlobalPhi43.MW20
