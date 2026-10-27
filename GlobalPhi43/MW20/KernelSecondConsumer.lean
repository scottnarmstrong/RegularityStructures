module

public import GlobalPhi43.MW20.KernelReconstruction

/-! Exact separation of the signed Lemma 2.10 estimate for the actual compact
MW20 kernel, with all integrability supplied by source continuity. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- The literal separated Lemma 2.10 left side equals the combined test. -/
theorem pastSmooth_second_consumer_separated (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (v J V : ParabolicSpace → ℝ)
    (hv : Continuous v) (hJ : Continuous J) (hV : Continuous V) (C₂ : ℝ) (x : ParabolicSpace) :
    pastSmooth (infiniteKernelMeasure Φ hΦ T hT)
      (fun y => (v y - v x) * V y + 3 * C₂ * (v y + J y)) x =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => (v y - v x) * V y) x +
        3 * C₂ * (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x +
          pastSmooth (infiniteKernelMeasure Φ hΦ T hT) J x) := by
  have hi := reconstruction_kernel_section_integrable Φ hΦ hT hT₁
    (fun y => (v y - v x) * V y) ((hv.sub continuous_const).mul hV) x
  have hiv := reconstruction_kernel_section_integrable Φ hΦ hT hT₁ v hv x
  have hij := reconstruction_kernel_section_integrable Φ hΦ hT hT₁ J hJ x
  have hic : Integrable (fun z => 3 * C₂ * (v (x + z) + J (x + z)))
      (infiniteKernelMeasure Φ hΦ T hT) := by
    simpa only [Pi.add_apply] using (hiv.add hij).const_mul (3 * C₂)
  unfold pastSmooth
  change (∫ z, (v (x + z) - v x) * V (x + z) + 3 * C₂ * (v (x + z) + J (x + z))
    ∂infiniteKernelMeasure Φ hΦ T hT) = _
  rw [integral_add hi hic, integral_const_mul, integral_add hiv hij]

end GlobalPhi43.MW20
