module

public import GlobalPhi43.MW20.KernelDensityIntegral
public import GlobalPhi43.MW20.InfiniteKernel
public import GlobalPhi43.MW20.Setting.MWKernelSeq
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Identification of the n+1 finite convolution factors with the MW20 kernels. -/

public section
namespace GlobalPhi43.MW20
open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

theorem scaledKernelProfile_eq_parabolicRescale (Φ : ParabolicSpace → ℝ) (T : ℝ) :
    scaledKernelProfile Φ T = parabolicRescale Φ T := by
  funext z
  simp only [scaledKernelProfile,rescaledTestFunction,sub_zero,parabolicRescale,
    parabolicDilate,zpow_neg,zpow_ofNat]
  congr 2
  ext <;> simp [div_eq_mul_inv,inv_pow,mul_comm]

/-- The density formula fixes the convolution order, not just the resulting measure. -/
theorem probabilityConvolution_map_parabolicDilate (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {c : ℝ} (hc : 0<c) (f : ParabolicSpace →ᵇ ℝ) (x : ParabolicSpace) :
    letI := kernelProfileMeasure_probability Φ hΦ
    probabilityConvolution ((kernelProfileMeasure Φ).map (parabolicDilate c)) f x =
      convolution f (parabolicRescale Φ c) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have := kernelProfileMeasure_probability Φ hΦ
  have : Measure.IsAddHaarMeasure (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let g := f.compContinuous (⟨fun y => x-y,continuous_const.sub continuous_id⟩ : C(ParabolicSpace,ParabolicSpace))
  have h := integral_scaledKernelMeasure Φ hΦ hc g
  rw [probabilityConvolution_apply]
  change (∫ y, g y ∂(kernelProfileMeasure Φ).map (parabolicDilate c)) = _
  rw [h]
  simp only [convolution,ContinuousLinearMap.lsmul_apply,smul_eq_mul,
    scaledKernelProfile_eq_parabolicRescale, g,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk]
  rw [← integral_sub_left_eq_self (fun y => f y * parabolicRescale Φ c (x-y)) volume x]
  simp only [sub_sub_self]
  apply integral_congr_ae
  exact ae_of_all _ fun y => mul_comm _ _

/-- Both sides have n+1 actual factors, with scales T/2 through T/2^(n+1). -/
theorem mwKernelSeq_eq_finiteKernelDensity (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (n : ℕ) (x : ParabolicSpace) :
    mwKernelSeq Φ T n x = finiteKernelDensity Φ hΦ T hT n x := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing x with
  | zero =>
    change parabolicRescale Φ (T/2) x = scaledKernelSeed Φ hΦ (T/2) (half_pos hT) x
    rw [scaledKernelSeed,compactSmoothSeed_apply,scaledKernelProfile_eq_parabolicRescale]
  | succ n ih =>
    simp only [mwKernelSeq]
    have he : mwKernelSeq Φ T n = finiteKernelDensity Φ hΦ T hT n := funext ih
    rw [he]
    change _ = probabilityConvolution
      ((kernelProfileMeasure Φ).map (parabolicDilate ((T/2)/2^(n+1))))
      (finiteKernelDensity Φ hΦ T hT n) x
    rw [probabilityConvolution_map_parabolicDilate Φ hΦ (by positivity)]
    congr 2
    rw [pow_succ]
    ring

end GlobalPhi43.MW20
