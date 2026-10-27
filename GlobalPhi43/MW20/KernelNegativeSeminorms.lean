module

public import GlobalPhi43.MW20.KernelReconstruction
public import GlobalPhi43.MW20.NegativeSeminorms

/-! Source negative seminorms attached to the actual constructed MW20 kernel.
The values at nonpositive scales are irrelevant to every source supremum. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- A total scale family for the actual constructed MW20 kernels. -/
@[expose] noncomputable def mw20TestingKernel (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (t : ℝ) : Measure ParabolicSpace :=
  if ht : 0 < t then infiniteKernelMeasure Φ hΦ t ht else 0

/-- Every positive-scale member is exactly the actual infinite kernel. -/
theorem mw20TestingKernel_pos (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) :
    mw20TestingKernel Φ hΦ t = infiniteKernelMeasure Φ hΦ t ht := by
  simp only [mw20TestingKernel, dite_eq_left ht]

end GlobalPhi43.MW20
