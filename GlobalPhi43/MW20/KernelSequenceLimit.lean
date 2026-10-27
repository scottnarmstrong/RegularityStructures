module

public import GlobalPhi43.MW20.FiniteKernelIdentity
public import GlobalPhi43.MW20.Setting.MWKernel

/-! The pointwise kernel limit equals the uniform limit of the finite convolutions. -/

public section
namespace GlobalPhi43.MW20
open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

theorem mwKernelSeq_tendsto_infiniteKernel (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1) (x : ParabolicSpace) :
    Tendsto (fun n => mwKernelSeq Φ T n x) atTop (𝓝 (infiniteKernel Φ hΦ T hT x)) := by
  have h := ((BoundedContinuousFunction.lipschitz_eval_const x).continuous).tendsto
    (infiniteKernel Φ hΦ T hT)
  simpa only [Function.comp_def,mwKernelSeq_eq_finiteKernelDensity Φ hΦ hT] using
    h.comp (finiteKernelDensity_tendsto Φ hΦ hT hT1)

/-- No paired-characterisation axiom or limit certificate is supplied. -/
theorem mwKernel_eq_infiniteKernel (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1) (x : ParabolicSpace) :
    mwKernel Φ T x = infiniteKernel Φ hΦ T hT x :=
  (mwKernelSeq_tendsto_infiniteKernel Φ hΦ hT hT1 x).limUnder_eq

end GlobalPhi43.MW20
