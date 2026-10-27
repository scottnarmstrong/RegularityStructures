module

public import GlobalPhi43.Invariant.KrylovBogoliubov

/-! # Invariance of one supplied weak limit of orbit averages -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

variable {E : Type*} [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [PolishSpace E] in
/-- A weak limit of orbit averages has equal integrals of f and P_s f.
The same probability mu is fixed before s and f are selected. -/
theorem weakLimit_action_eq
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (hFeller : ∀ s (f : E →ᵇ ℝ), Continuous (fun x => ∫ y, f y ∂K s x))
    (ρ : Kernel ℝ E) [IsMarkovKernel ρ] (x : E)
    (horbit : ∀ t (ht : 0 ≤ t), ρ t = K ⟨t, ht⟩ x)
    (hsemi : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {ν : ℕ → ProbabilityMeasure E} (hν : ∀ n, (ν n : Measure E) = fullAverage ρ (T n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto ν atTop (𝓝 μ))
    (s : ℝ≥0) (f : E →ᵇ ℝ) :
    (∫ y, (∫ z, f z ∂K s y) ∂(μ : Measure E)) = ∫ y, f y ∂(μ : Measure E) := by
  let Pf := fellerAction (K s) (hFeller s) f
  have hPf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) Pf
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  have hz : Tendsto (fun n => (∫ y, Pf y ∂(ν n : Measure E)) -
      ∫ y, f y ∂(ν n : Measure E)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n in atTop,
        ‖(∫ y, Pf y ∂(ν n : Measure E)) - ∫ y, f y ∂(ν n : Measure E)‖ ≤
          (2 * s / T n) * ‖f‖ := by
      filter_upwards [hT.eventually_gt_atTop 0] with n hn
      rw [hν n]
      exact abs_fullAverage_action_sub_le K ρ x horbit hsemi s hn f
    apply squeeze_zero_norm' hbound
    have h := ((tendsto_const_nhds (x := 2 * (s : ℝ))).mul
      (tendsto_inv_atTop_zero.comp hT)).mul
      (tendsto_const_nhds (x := ‖f‖))
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, zero_mul] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique (hPf.sub hf) hz)

/-- The conditional KB invariance conclusion, as equality of Borel probability measures. -/
theorem weakLimit_invariant
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (hFeller : ∀ s (f : E →ᵇ ℝ), Continuous (fun x => ∫ y, f y ∂K s x))
    (ρ : Kernel ℝ E) [IsMarkovKernel ρ] (x : E)
    (horbit : ∀ t (ht : 0 ≤ t), ρ t = K ⟨t, ht⟩ x)
    (hsemi : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {ν : ℕ → ProbabilityMeasure E} (hν : ∀ n, (ν n : Measure E) = fullAverage ρ (T n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto ν atTop (𝓝 μ)) (s : ℝ≥0) :
    (K s) ∘ₘ (μ : Measure E) = (μ : Measure E) := by
  have he : (⟨(K s) ∘ₘ (μ : Measure E), inferInstance⟩ : FiniteMeasure E) =
      (μ.toFiniteMeasure) := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ y, f y ∂(μ : Measure E).bind (K s)) = ∫ y, f y ∂(μ : Measure E)
    rw [integral_bind_bounded (μ : Measure E) (K s) f.continuous.measurable ‖f‖
      (fun y => f.norm_coe_le_norm y)]
    exact weakLimit_action_eq K hFeller ρ x horbit hsemi hT hν hμ s f
  exact congrArg FiniteMeasure.toMeasure he

end GlobalPhi43.Invariant
