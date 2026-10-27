module

public import GlobalPhi43.MW20.InfiniteKernelBlock
public import GlobalPhi43.MW20.InfiniteKernelSupport
public import GlobalPhi43.MW20.ConvolutionPairing
public import GlobalPhi43.MW20.FiniteSmoothing

/-! The reflected infinite smoothing definition for the constructed kernel measure. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- Ordinary source smoothing, with relative kernel variable y-x. -/
@[expose] noncomputable def infinitePastSmooth (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T)
    (f : ParabolicSpace → ℝ) (x : ParabolicSpace) : ℝ :=
  ∫ y, infiniteKernel Φ hΦ T hT y * f (x + y)

end GlobalPhi43.MW20
