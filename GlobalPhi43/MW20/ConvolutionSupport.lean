module

public import GlobalPhi43.MW20.ConvolutionLimit

/-!
# Support propagation for actual probability averages
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A convolution adds at most the radius of its averaging measure. -/
theorem probabilityConvolution_eq_zero_of_norm_gt (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) {R r : ℝ} (hf : ∀ x, R < ‖x‖ → f x = 0)
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ r) {x : E} (hx : R + r < ‖x‖) :
    probabilityConvolution μ f x = 0 := by
  rw [probabilityConvolution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  apply hf
  have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  linarith

/-- A prescribed radius sequence controls every finite average. -/
theorem convolutionIter_eq_zero_of_norm_gt (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E →ᵇ F) (R r : ℕ → ℝ)
    (hseed : ∀ x, R 0 < ‖x‖ → f x = 0)
    (hR : ∀ n, R (n + 1) = R n + r n)
    (hμ : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ r n) (n : ℕ) :
    ∀ x, R n < ‖x‖ → convolutionIter μ f n x = 0 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro x hx
    rw [hR] at hx
    exact probabilityConvolution_eq_zero_of_norm_gt (μ n) _ ih (hμ n) hx

/-- Support propagation for a subadditive gauge, including the exact source
max-parabolic distance. -/
theorem convolutionIter_eq_zero_of_gauge_gt (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E →ᵇ F) (ρ : E → ℝ)
    (hρ : ∀ x y, ρ x ≤ ρ (x - y) + ρ y) (R r : ℕ → ℝ)
    (hseed : ∀ x, R 0 < ρ x → f x = 0)
    (hR : ∀ n, R (n + 1) = R n + r n)
    (hμ : ∀ n, ∀ᵐ y ∂μ n, ρ y ≤ r n) (n : ℕ) :
    ∀ x, R n < ρ x → convolutionIter μ f n x = 0 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro x hx
    rw [hR] at hx
    change (∫ y, convolutionIter μ f n (x - y) ∂μ n) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [hμ n] with y hy
    apply ih
    have ht := hρ x y
    linarith

end GlobalPhi43.MW20
