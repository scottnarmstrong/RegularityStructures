module

public import GlobalPhi43.Markov.FlowKernel
public import GlobalPhi43Statements.Defs.AveragedLaw
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Normalized interval averages of measurable probability laws -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E : Type*} [MeasurableSpace E]

/-- A normalized average on (a,b]. The full average uses a=0 and the late average a=1. -/
def intervalAverage (κ : Kernel ℝ E) (a b : ℝ) : Measure E :=
  (ENNReal.ofReal (b - a))⁻¹ • (volume.restrict (Ioc a b)).bind κ

/-- Evaluation of the average is the normalized integral of the law evaluations. -/
theorem intervalAverage_apply (κ : Kernel ℝ E) (a b : ℝ) {S : Set E}
    (hS : MeasurableSet S) :
    intervalAverage κ a b S =
      (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ t in Ioc a b, κ t S := by
  simp only [intervalAverage, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply hS κ.measurable.aemeasurable]

/-- An average of probability laws over a nonempty finite interval is a probability. -/
theorem intervalAverage_isProbabilityMeasure (κ : Kernel ℝ E) [IsMarkovKernel κ]
    {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (intervalAverage κ a b) := by
  constructor
  rw [intervalAverage_apply κ a b MeasurableSet.univ]
  simp only [measure_univ, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, one_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))
    ENNReal.ofReal_ne_top

/-- Nonnegative measurable tests commute with the normalized law average. -/
theorem lintegral_intervalAverage (κ : Kernel ℝ E) (a b : ℝ)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂intervalAverage κ a b =
      (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ t in Ioc a b, ∫⁻ x, f x ∂κ t := by
  rw [intervalAverage, lintegral_smul_measure,
    Measure.lintegral_bind κ.measurable.aemeasurable hf.aemeasurable]
  rfl

/-- Bounded tests commute with binding a finite measure against probability laws. -/
theorem integral_bind_bounded {A : Type*} [MeasurableSpace A]
    (m : Measure A) [IsFiniteMeasure m]
    (κ : Kernel A E) [IsMarkovKernel κ] {f : E → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂m.bind κ) = ∫ t, ∫ x, f x ∂κ t ∂m := by
  have : IsFiniteMeasure (m.bind κ) :=
    inferInstanceAs (IsFiniteMeasure (κ ∘ₘ m))
  have hi : Integrable f (m.bind κ) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hb)
  exact Kernel.integral_comp (κ := Kernel.const Unit m) (η := κ) (a := ()) hi

/-- Bounded Borel real tests commute with the normalized law average. -/
theorem integral_intervalAverage (κ : Kernel ℝ E) [IsMarkovKernel κ] (a b : ℝ)
    {f : E → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    ∫ x, f x ∂intervalAverage κ a b =
      (b - a)⁻¹ * ∫ t in Ioc a b, ∫ x, f x ∂κ t := by
  let m : Measure ℝ := volume.restrict (Ioc a b)
  have he : (∫ x, f x ∂m.bind κ) = ∫ t, ∫ x, f x ∂κ t ∂m :=
    integral_bind_bounded m κ hf C hb
  rw [intervalAverage, integral_smul_measure, he]
  by_cases hab : a ≤ b
  · rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    rfl
  · have hempty : Ioc a b = ∅ := Ioc_eq_empty (not_lt_of_ge (le_of_not_ge hab))
    simp [hempty, m]

/-- Full average of a measurable probability-law kernel. -/
def fullAverage (κ : Kernel ℝ E) (T : ℝ) : Measure E := intervalAverage κ 0 T

/-- Late average, with the exact denominator T-1. -/
def lateAverage (κ : Kernel ℝ E) (T : ℝ) : Measure E := intervalAverage κ 1 T

/-- Measurable laws on nonnegative times extend to a probability-law kernel on R by
clipping the time at zero. No flow property is assumed. -/
def nonnegativeLawKernel (laws : Ici (0 : ℝ) → Measure E) (hm : Measurable laws) :
    Kernel ℝ E where
  toFun t := laws ⟨max 0 t, le_max_left _ _⟩
  measurable' := hm.comp ((measurable_const.max measurable_id).subtype_mk)

/-- On nonnegative times clipping leaves the supplied law unchanged. -/
theorem nonnegativeLawKernel_apply (laws : Ici (0 : ℝ) → Measure E)
    (hm : Measurable laws) {t : ℝ} (ht : 0 ≤ t) :
    nonnegativeLawKernel laws hm t = laws ⟨t, ht⟩ := by
  change laws ⟨max 0 t, _⟩ = laws ⟨t, ht⟩
  simp only [max_eq_right ht]

/-- Identification of the full average, including its inverse time mass,
under explicit law measurability. -/
theorem averagedLaw_eq_fullAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {η : RegularityStructures.NegExponent}
    (u : ℝ → ℝ → RegularityStructures.HolderBesov η → Ω →
      RegularityStructures.HolderBesov η)
    (hm : Measurable (fun t : Ici (0 : ℝ) => flowLaw P u t 0)) (T : ℝ) :
    averagedLaw P u T =
      fullAverage (nonnegativeLawKernel (fun t => flowLaw P u t 0) hm) T := by
  unfold averagedLaw fullAverage intervalAverage
  rw [sub_zero]
  congr 1
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (nonnegativeLawKernel_apply _ hm ht.1.le).symm

end GlobalPhi43.Invariant
