module

public import GlobalPhi43.MW20.KernelNegativeSeminorms

/-! Translate the actual compact kernel measure to its source test centre.
This connects the existing source-germ algebra with reconstruction. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Testing a continuous field against the translated kernel is precisely
past-looking smoothing; this introduces no density or integrability premise. -/
theorem integral_centered_measure (ν : Measure ParabolicSpace) (x : ParabolicSpace)
    (f : ParabolicSpace → ℝ) (hf : Continuous f) :
    (∫ y, f y ∂ν.map (fun z => x + z)) = pastSmooth ν f x :=
  integral_map (by fun_prop) hf.aestronglyMeasurable

/-- Translated-kernel integrability for every continuous source field. -/
theorem reconstruction_centered_integrable (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (x : ParabolicSpace)
    (f : ParabolicSpace → ℝ) (hf : Continuous f) :
    Integrable f ((infiniteKernelMeasure Φ hΦ t ht).map (fun z => x + z)) := by
  exact (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2
    (reconstruction_kernel_section_integrable Φ hΦ ht ht₁ f hf x)

end GlobalPhi43.MW20
