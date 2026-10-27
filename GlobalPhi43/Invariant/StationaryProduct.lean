module

public import GlobalPhi43.Invariant.StationaryChains
public import GlobalPhi43.Markov.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Prod

/-! # The selected flow on the literal product probability space -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace GlobalPhi43.Invariant

open GlobalPhi43.Markov

variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]

/-- A parameter-dependent sample on P.prod mu has the mixture of its deterministic
parameter laws. This uses the literal coordinate process, not a new process with matching laws. -/
theorem map_product_eq_kernel_comp (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ] (U : Ω × E → F) (hU : Measurable U)
    (κ : Kernel E F) (hlaw : ∀ x, κ x = P.map (fun ω => U (ω, x))) :
    (P.prod μ).map U = κ ∘ₘ μ := by
  ext S hS
  rw [Measure.map_apply hU hS, Measure.prod_apply_symm (hU hS)]
  change (∫⁻ x, P ((fun ω => (ω, x)) ⁻¹' U ⁻¹' S) ∂μ) = (μ.bind κ) S
  rw [Measure.bind_apply hS κ.measurable.aemeasurable]
  apply lintegral_congr
  intro x
  have hx : Measurable (fun ω => U (ω, x)) := hU.comp measurable_prodMk_right
  rw [hlaw x, Measure.map_apply hx hS]
  rfl

/-- A jointly measurable selected process and its scalar Markov identities give
the finite-vector product-space law, with no finite-dimensional law premise. -/
theorem product_map_observations_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (U : ℝ≥0 → E → Ω → E) (hjoint : ∀ s, Measurable (fun p : Ω × E => U s p.2 p.1))
    (m : ℝ≥0 → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (ha : ∀ s x, Measurable[m s] (U s x)) (hzero : ∀ x, U 0 x =ᵐ[P] fun _ => x)
    (hc : ∀ s t, s ≤ t → ∀ x (g : E → ℝ), Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (U t x ω) | m s] =ᵐ[P]
        fun ω => ∫ y, g y ∂K (t - s) (U s x ω))
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    (P.prod μ).map (fun p (i : Fin (n + 1)) => U (t i) p.2 p.1) =
      observationChain K t ∘ₘ μ := by
  apply map_product_eq_kernel_comp P μ _ (Measurable.of_eval fun i => hjoint (t i))
    (observationChain K t)
  intro x
  exact (map_observations_eq_observationChain P K (fun s => U s x) m hm hmono
    (fun s => ha s x) x (hzero x) (fun s t hst => hc s t hst x) t ht).symm

/-- One supplied invariant mu makes all finite-dimensional laws shift invariant
on the same literal product space. No new measure is selected after a time or shift. -/
theorem product_fdd_stationary (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (hμ : ∀ s, K s ∘ₘ μ = μ)
    (U : ℝ≥0 → E → Ω → E) (hjoint : ∀ s, Measurable (fun p : Ω × E => U s p.2 p.1))
    (m : ℝ≥0 → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (ha : ∀ s x, Measurable[m s] (U s x)) (hzero : ∀ x, U 0 x =ᵐ[P] fun _ => x)
    (hc : ∀ s t, s ≤ t → ∀ x (g : E → ℝ), Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (U t x ω) | m s] =ᵐ[P]
        fun ω => ∫ y, g y ∂K (t - s) (U s x ω))
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (r : ℝ≥0) :
    (P.prod μ).map (fun p (i : Fin (n + 1)) => U (r + t i) p.2 p.1) =
      (P.prod μ).map (fun p (i : Fin (n + 1)) => U (t i) p.2 p.1) := by
  have hshift : Monotone (fun i => r + t i) := fun _ _ h => add_le_add le_rfl (ht h)
  rw [product_map_observations_eq P μ K U hjoint m hm hmono ha hzero hc
      (fun i => r + t i) hshift,
    product_map_observations_eq P μ K U hjoint m hm hmono ha hzero hc t ht]
  exact observationChain_comp_shift_eq K μ hμ t r

/-- Every one-time law of the literal selected flow is the same supplied invariant mu. -/
theorem product_oneTime_law (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ≥0 → Kernel E E) (hμ : ∀ s, K s ∘ₘ μ = μ)
    (U : ℝ≥0 → E → Ω → E) (hjoint : ∀ s, Measurable (fun p : Ω × E => U s p.2 p.1))
    (hlaw : ∀ s x, K s x = P.map (U s x)) (t : ℝ≥0) :
    (P.prod μ).map (fun p => U t p.2 p.1) = μ := by
  rw [map_product_eq_kernel_comp P μ _ (hjoint t) (K t) (hlaw t), hμ]

end GlobalPhi43.Invariant
