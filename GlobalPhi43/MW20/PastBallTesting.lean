module

public import GlobalPhi43.MW20.CylinderTesting

/-!
# The literal small-scale testing ball for the actual MW20 kernel
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- A point strictly inside the L past ball stays strictly inside L+T
under a closed-past radius-T shift, including support-boundary shifts. -/
theorem pastBall_add_closedPast {x y z : ParabolicSpace} {L T : ℝ}
    (hy : y ∈ Local.pastBall x L) (hzt : z.1 ≤ 0) (hz : Local.pdist 0 z ≤ T) :
    y + z ∈ Local.pastBall x (L + T) := by
  have he : Local.pdist y (y + z) = Local.pdist 0 z := by
    simp only [Local.pdist, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero,
      sub_add_eq_sub_sub, sub_self, zero_sub]
  have ht := Local.pdist_triangle x y (y + z)
  rw [he] at ht
  refine ⟨by linarith [hy.1], ?_⟩
  change y.1 + z.1 < x.1
  linarith [hy.2]

/-- The actual kernel tests only the paper's L+T past ball. -/
theorem infiniteKernelMeasure_ae_pastBall (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T L : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {x y : ParabolicSpace}
    (hy : y ∈ Local.pastBall x L) :
    ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT, y + z ∈ Local.pastBall x (L + T) := by
  filter_upwards [infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT1] with z hz
  exact pastBall_add_closedPast hy hz.1 hz.2

/-- Literal testing-ball containment supplies actual almost-everywhere
sampling in any source domain, with no independent integrability premise. -/
theorem infiniteKernelMeasure_ae_testingDomain (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T L : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {x y : ParabolicSpace}
    {D : Set ParabolicSpace} (hball : Local.pastBall x (L + T) ⊆ D)
    (hy : y ∈ Local.pastBall x L) :
    ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT, y + z ∈ D :=
  (infiniteKernelMeasure_ae_pastBall Φ hΦ hT hT1 hy).mono fun _ hz => hball hz

end GlobalPhi43.MW20
