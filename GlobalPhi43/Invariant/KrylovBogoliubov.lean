module

public import GlobalPhi43.Invariant.Averages
public import GlobalPhi43.Invariant.Prokhorov
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Conditional Krylov--Bogoliubov for supplied measurable Feller kernels

This file does not construct a flow. The orbit laws, semigroup identity and Feller
continuity are explicit premises. All limit assertions use the same supplied weak limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

/-- A measurable bounded real function is integrable on every finite interval. -/
theorem intervalIntegrable_of_measurable_bounded {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hb : ∀ t, ‖g t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable g volume a b := by
  apply intervalIntegrable_iff.mpr
  change Integrable g (volume.restrict (Ioc (min a b) (max a b)))
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)

/-- The two end intervals give the exact shift constant, even when s exceeds T. -/
theorem abs_integral_shift_sub_le {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ t, ‖g t‖ ≤ C) {s : ℝ} (hs : 0 ≤ s) (T : ℝ) :
    |(∫ t in s..T + s, g t) - ∫ t in 0..T, g t| ≤ 2 * s * C := by
  have hi := intervalIntegrable_of_measurable_bounded hg hb
  rw [intervalIntegral.integral_interval_sub_interval_comm (hi s (T + s))
    (hi 0 T) (hi s 0)]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := 0) (fun t _ => hb t)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T + s) (b := T) (fun t _ => hb t)
  have he : T - (T + s) = -s := by ring
  simp only [Real.norm_eq_abs, zero_sub, he, abs_neg, abs_of_nonneg hs] at h1 h2
  exact (abs_sub _ _).trans (by linarith)

variable {E : Type*} [MeasurableSpace E]

/-- A bounded test remains bounded, with norm one, under a probability kernel. -/
theorem norm_kernel_integral_le (κ : Kernel E E) [IsMarkovKernel κ]
    [TopologicalSpace E] (f : E →ᵇ ℝ) (x : E) :
    ‖∫ y, f y ∂κ x‖ ≤ ‖f‖ := by
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := κ x)
      (ae_of_all _ fun y => f.norm_coe_le_norm y))

variable [TopologicalSpace E] [BorelSpace E]

/-- Feller continuity makes the kernel action a bounded continuous test. -/
def fellerAction (κ : Kernel E E) [IsMarkovKernel κ]
    (hκ : ∀ f : E →ᵇ ℝ, Continuous (fun x => ∫ y, f y ∂κ x))
    (f : E →ᵇ ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup _ (hκ f) ‖f‖
    (norm_kernel_integral_le κ f)

/-- A law kernel records the orbit of x under a nonnegative-time semigroup. -/
theorem integral_orbit_action (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (ρ : Kernel ℝ E) (x : E)
    (horbit : ∀ t (ht : 0 ≤ t), ρ t = K ⟨t, ht⟩ x)
    (hsemi : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (s : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (f : E →ᵇ ℝ) :
    (∫ y, (∫ z, f z ∂K s y) ∂ρ t) = ∫ y, f y ∂ρ (t + s) := by
  rw [horbit t ht, horbit (t + s) (add_nonneg ht s.2)]
  change (∫ y, (∫ z, f z ∂K s y) ∂K (NNReal.mk t ht) x) =
    ∫ y, f y ∂K (NNReal.mk t ht + s) x
  rw [hsemi]
  exact (Kernel.integral_comp (Integrable.of_bound
    f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun y => f.norm_coe_le_norm y))).symm

/-- The KB shift estimate, conditional only on the supplied orbit and semigroup data. -/
theorem abs_fullAverage_action_sub_le
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (ρ : Kernel ℝ E) [IsMarkovKernel ρ] (x : E)
    (horbit : ∀ t (ht : 0 ≤ t), ρ t = K ⟨t, ht⟩ x)
    (hsemi : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (s : ℝ≥0) {T : ℝ} (hT : 0 < T) (f : E →ᵇ ℝ) :
    |(∫ y, (∫ z, f z ∂K s y) ∂fullAverage ρ T) -
      ∫ y, f y ∂fullAverage ρ T| ≤ (2 * s / T) * ‖f‖ := by
  let g : ℝ → ℝ := fun t => ∫ y, f y ∂ρ t
  have hg : Measurable g := f.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  have hb (t : ℝ) : ‖g t‖ ≤ ‖f‖ := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ρ t)
        (ae_of_all _ fun y => f.norm_coe_le_norm y))
  have hact : Measurable (fun y => ∫ z, f z ∂K s y) :=
    f.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  rw [fullAverage, integral_intervalAverage _ _ _ hact ‖f‖
      (norm_kernel_integral_le (K s) f),
    integral_intervalAverage _ _ _ f.continuous.measurable ‖f‖
      (fun y => f.norm_coe_le_norm y)]
  have he : (∫ t in Ioc 0 T, ∫ y, (∫ z, f z ∂K s y) ∂ρ t) =
      ∫ t in Ioc 0 T, g (t + s) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact integral_orbit_action K ρ x horbit hsemi s t ht.1.le f
  rw [he, ← intervalIntegral.integral_of_le hT.le,
    ← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_comp_add_right, zero_add, sub_zero, ← mul_sub,
    abs_mul, abs_of_nonneg (inv_nonneg.mpr hT.le)]
  have hshift := abs_integral_shift_sub_le hg hb s.2 T
  calc
    T⁻¹ * |(∫ t in (s : ℝ)..T + s, g t) - ∫ t in 0..T, g t| ≤
        T⁻¹ * (2 * s * ‖f‖) := mul_le_mul_of_nonneg_left hshift (inv_nonneg.mpr hT.le)
    _ = (2 * s / T) * ‖f‖ := by ring

end GlobalPhi43.Invariant
