module

public import GlobalPhi43.Markov.ConditionalMarkov
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace GlobalPhi43.Markov

/-- A conditional Markov identity yields both orders of the time-semigroup action.
The random maps and their conditional laws are explicit hypotheses. -/
theorem kernel_action_semigroup_of_conditional {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ≥0 → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (U : ℝ≥0 → E → Ω → E) (m : ℝ≥0 → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hU : ∀ t x, Measurable (U t x))
    (hK : ∀ t x, K t x = P.map (U t x))
    (hc : ∀ s t x (f : E → ℝ), Measurable f → (∃ C, ∀ y, |f y| ≤ C) →
      P[fun ω => f (U (s + t) x ω) | m s] =ᵐ[P]
        fun ω => ∫ y, f y ∂K t (U s x ω))
    (s t : ℝ≥0) {f : E → ℝ} (hf : Measurable f) (hb : ∃ C, ∀ y, |f y| ≤ C) (x : E) :
    (∫ y, f y ∂K (s + t) x) = (∫ y, (∫ z, f z ∂K t y) ∂K s x) ∧
    (∫ y, f y ∂K (s + t) x) = (∫ y, (∫ z, f z ∂K s y) ∂K t x) := by
  have hact (a b : ℝ≥0) :
      (∫ y, f y ∂K (a + b) x) = ∫ y, (∫ z, f z ∂K b y) ∂K a x := by
    rw [hK (a + b) x, integral_map (hU (a + b) x).aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
      hK a x]
    exact integral_eq_iterated_of_conditional P (hm a) (hU a x) (K b) hf (hc a b x f hf hb)
  exact ⟨hact s t, by simpa only [add_comm t s] using hact t s⟩

/-- Finite measures are determined by their bounded Borel real integrals. -/
theorem measure_eq_of_bounded_integrals {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : E → ℝ, Measurable f → (∃ C, ∀ y, |f y| ≤ C) →
      (∫ y, f y ∂μ) = ∫ y, f y ∂ν) : μ = ν := by
  classical
  ext A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp
  have hb : ∃ C : ℝ, ∀ y, |A.indicator (fun _ => (1 : ℝ)) y| ≤ C := by
    refine ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ A <;> simp [hy]
  have he := h (A.indicator (fun _ => 1)) (measurable_const.indicator hA) hb
  simpa only [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using he

/-- The action semigroup identity gives equality of probability kernels, hence the setwise
Chapman-Kolmogorov identity. -/
theorem kernel_eq_comp_of_action {E : Type*} [MeasurableSpace E]
    (κ η θ : Kernel E E) [IsMarkovKernel κ] [IsMarkovKernel η] [IsMarkovKernel θ]
    (h : ∀ x (f : E → ℝ), Measurable f → (∃ C, ∀ y, |f y| ≤ C) →
      (∫ z, f z ∂θ x) = ∫ y, (∫ z, f z ∂η y) ∂κ x) : θ = η ∘ₖ κ := by
  apply Kernel.ext
  intro x
  apply measure_eq_of_bounded_integrals
  intro f hf hb
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable f ((η ∘ₖ κ) x) := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hC y)
  rw [Kernel.integral_comp hi]
  exact h x f hf ⟨C, hC⟩

/-- Generic measurable-kernel semigroup machinery from conditional Markov identities.
Both composition orders hold for the same fixed kernel family. -/
theorem kernel_semigroup_of_conditional {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ≥0 → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (U : ℝ≥0 → E → Ω → E) (m : ℝ≥0 → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hU : ∀ t x, Measurable (U t x))
    (hK : ∀ t x, K t x = P.map (U t x))
    (hc : ∀ s t x (f : E → ℝ), Measurable f → (∃ C, ∀ y, |f y| ≤ C) →
      P[fun ω => f (U (s + t) x ω) | m s] =ᵐ[P]
        fun ω => ∫ y, f y ∂K t (U s x ω)) (s t : ℝ≥0) :
    K (s + t) = K t ∘ₖ K s ∧ K (s + t) = K s ∘ₖ K t := by
  constructor
  · apply kernel_eq_comp_of_action
    intro x f hf hb
    exact (kernel_action_semigroup_of_conditional P K U m hm hU hK hc s t hf hb x).1
  · apply kernel_eq_comp_of_action
    intro x f hf hb
    exact (kernel_action_semigroup_of_conditional P K U m hm hU hK hc s t hf hb x).2

end GlobalPhi43.Markov
