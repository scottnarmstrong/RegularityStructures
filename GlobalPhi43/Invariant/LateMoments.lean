module

public import GlobalPhi43.Invariant.Averages
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Uniform one-event restart estimates and late-average moments -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

omit [MeasurableSpace E] in
/-- A bound on one event for every datum can be evaluated at the random restarted datum.
The event is selected before the datum; separately almost-sure bounds do not suffice. -/
theorem restarted_bound_ae (P : Measure Ω) (u : ℝ → ℝ → E → Ω → E)
    (N : E → ℝ≥0∞) (B : ℝ → Ω → ℝ≥0∞)
    (hstep : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P, ∀ z, N (u t (t - 1) z ω) ≤ B t ω)
    (hrestart : ∀ t, 1 ≤ t → ∀ z ω,
      u t 0 z ω = u t (t - 1) (u (t - 1) 0 z ω) ω)
    {t : ℝ} (ht : 1 ≤ t) (z : E) :
    ∀ᵐ ω ∂P, N (u t 0 z ω) ≤ B t ω := by
  filter_upwards [hstep t ht] with ω hω
  rw [hrestart t ht]
  exact hω (u (t - 1) 0 z ω)

/-- Moment transfer from the actual restarted majorant to the orbit law. -/
theorem law_moment_of_restarted_bound (P : Measure Ω)
    (u : ℝ → ℝ → E → Ω → E) (N : E → ℝ≥0∞) (hN : Measurable N)
    (B : ℝ → Ω → ℝ≥0∞) (p : ℝ) (hp : 0 ≤ p) (C : ℝ≥0∞)
    (hstep : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P, ∀ z, N (u t (t - 1) z ω) ≤ B t ω)
    (hrestart : ∀ t, 1 ≤ t → ∀ z ω,
      u t 0 z ω = u t (t - 1) (u (t - 1) 0 z ω) ω)
    (hB : ∀ t, 1 ≤ t → ∫⁻ ω, B t ω ^ p ∂P ≤ C)
    {t : ℝ} (ht : 1 ≤ t) (z : E) (hu : Measurable (u t 0 z)) :
    ∫⁻ y, N y ^ p ∂P.map (u t 0 z) ≤ C := by
  have hm : Measurable (fun y => N y ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hN
  rw [lintegral_map hm hu]
  exact (lintegral_mono_ae ((restarted_bound_ae P u N B hstep hrestart ht z).mono
    fun _ h => ENNReal.rpow_le_rpow h hp)).trans (hB t ht)

/-- Uniform late-time moments integrate with the exact normalization T-1. -/
theorem lintegral_lateAverage_le (ρ : Kernel ℝ E) {g : E → ℝ≥0∞}
    (hg : Measurable g) {C : ℝ≥0∞}
    (hC : ∀ t, 1 < t → ∫⁻ y, g y ∂ρ t ≤ C)
    {T : ℝ} (hT : 1 < T) : ∫⁻ y, g y ∂lateAverage ρ T ≤ C := by
  rw [lateAverage, lintegral_intervalAverage ρ 1 T hg]
  have hbound : (∫⁻ t in Ioc (1 : ℝ) T, ∫⁻ y, g y ∂ρ t) ≤
      C * ENNReal.ofReal (T - 1) := by
    apply (setLIntegral_mono' measurableSet_Ioc (fun t ht => hC t ht.1)).trans
    simp
  calc
    _ ≤ (ENNReal.ofReal (T - 1))⁻¹ * (C * ENNReal.ofReal (T - 1)) :=
      mul_le_mul_right hbound _
    _ = C := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hT))) ENNReal.ofReal_ne_top,
        mul_one]

end GlobalPhi43.Invariant
