module

public import GlobalPhi43.MW20.KernelParabolicSupport
public import GlobalPhi43.MW20.InfiniteKernelMeasure

/-!
# The exact closed-past support formulation for the infinite probability measure
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Every finite density vanishes at strictly future relative times. -/
theorem finiteKernelDensity_eq_zero_of_time_pos (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (n : ℕ)
    {x : ParabolicSpace} (hx : 0 < x.1) : finiteKernelDensity Φ hΦ T hT n x = 0 := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing x with
  | zero =>
    by_contra hn
    have hb := (scaledKernelSeed_parabolic_support Φ hΦ (half_pos hT) hn).1
    linarith
  | succ n ih =>
    change (∫ y, finiteKernelDensity Φ hΦ T hT n (x - y)
      ∂dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) n) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [dyadicKernelFactor_ae_parabolic Φ hΦ (half_pos hT).le n] with y hy
    apply ih
    change 0 < x.1 - y.1
    linarith [hy.1]

/-- The limiting density vanishes outside the exact closed past ball. -/
theorem infiniteKernel_closedPast_support (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {x : ParabolicSpace}
    (hx : infiniteKernel Φ hΦ T hT x ≠ 0) :
    x.1 ≤ 0 ∧ Local.pdist 0 x ≤ T := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT1)).tendsto_at x
  constructor
  · by_contra hn
    apply hx
    apply tendsto_nhds_unique ht
    simpa only [finiteKernelDensity_eq_zero_of_time_pos Φ hΦ hT _ (lt_of_not_ge hn)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · by_contra hn
    apply hx
    apply tendsto_nhds_unique ht
    simpa only [finiteKernelDensity_eq_zero_of_pdist_gt Φ hΦ hT _ (lt_of_not_ge hn)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Closed-past support of the infinite kernel measure for local reconstruction. -/
theorem infiniteKernelMeasure_ae_closedPast (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT,
      z.1 ≤ 0 ∧ Local.pdist 0 z ≤ T := by
  unfold infiniteKernelMeasure
  apply (ae_withDensity_iff
    (infiniteKernel Φ hΦ T hT).continuous.measurable.ennreal_ofReal).2
  apply ae_of_all
  intro z hz
  have hn : infiniteKernel Φ hΦ T hT z ≠ 0 := by
    intro he; simp [he] at hz
  exact infiniteKernel_closedPast_support Φ hΦ hT hT1 hn

end GlobalPhi43.MW20
