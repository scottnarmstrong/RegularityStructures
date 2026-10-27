module

public import GlobalPhi43.MW20.KernelPastSupport
public import GlobalPhi43.MW20.NegativeSeminorms

/-!
# Actual infinite-kernel tree tests for the first product

These attach the extended negative tree seminorms to the constructed MW20
kernel. The first product's reconstruction estimate is a separate obligation.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- The actual kernel family; nonpositive scales are unused by source norms. -/
@[expose] noncomputable def sourceKernelFamily (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) : Measure ParabolicSpace :=
  if hT : 0 < T then infiniteKernelMeasure Φ hΦ T hT else 0

@[simp] theorem sourceKernelFamily_pos (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) :
    sourceKernelFamily Φ hΦ T = infiniteKernelMeasure Φ hΦ T hT := by
  simp only [sourceKernelFamily, dite_eq_left hT]


end GlobalPhi43.MW20
