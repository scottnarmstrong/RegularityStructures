module

public import GlobalPhi43.MW20.DyadicKernelMeasure
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! The reflected smoothing definition. The kernel variable is added to the evaluation point; negative-time kernels therefore look into the past. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- Past-looking smoothing against a measure in the relative kernel variable. -/
@[expose] noncomputable def pastSmooth (μ : Measure ParabolicSpace)
    (f : ParabolicSpace → ℝ) (x : ParabolicSpace) : ℝ := ∫ z, f (x + z) ∂μ

end GlobalPhi43.MW20
