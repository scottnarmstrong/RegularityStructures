module

public import GlobalPhi43.MW20.AllScaleKernelMeasure
public import GlobalPhi43.MW20.InfinitePastSmoothing

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local

/-- Measure tests and density tests agree at every positive scale. -/
theorem pastSmooth_infinite_eq_density_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    pastSmooth (infiniteKernelMeasure Φ hΦ T hT) f x = infinitePastSmooth Φ hΦ T hT f x :=
  integral_infiniteKernelMeasure_all Φ hΦ hT _

/-- Exact source smoothing transport at all positive coordinate and test scales. -/
theorem infinitePastSmooth_parabolicPullback (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (a : ℝ) (f : ParabolicSpace → ℝ) (b : ParabolicSpace)
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T) (x : ParabolicSpace) :
    infinitePastSmooth Φ hΦ T hT (parabolicPullback a f b ℓ) x =
      a*infinitePastSmooth Φ hΦ (ℓ*T) (mul_pos hℓ hT) f (parabolicMap b ℓ x) := by
  have hh := integral_comp_parabolicDilate
    (fun w => infiniteKernel Φ hΦ (ℓ*T) (mul_pos hℓ hT) w *
      f (parabolicMap b ℓ x+w)) hℓ
  simp_rw [infiniteKernel_scale_dilate Φ hΦ hℓ hT,mul_assoc] at hh
  rw [integral_const_mul] at hh
  have hp := mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 5 hℓ.ne')) hh
  have hmap (w : ParabolicSpace) : parabolicMap b ℓ (x+w) =
      parabolicMap b ℓ x+parabolicDilate ℓ w := by
    simp only [parabolicMap,parabolicDilate,Prod.fst_add,Prod.snd_add,mul_add,smul_add,Prod.mk_add_mk,add_assoc]
  have hplain : infinitePastSmooth Φ hΦ T hT (fun y => f (parabolicMap b ℓ y)) x =
      infinitePastSmooth Φ hΦ (ℓ*T) (mul_pos hℓ hT) f (parabolicMap b ℓ x) := by
    simpa only [infinitePastSmooth,hmap] using hp
  rw [← hplain]
  unfold infinitePastSmooth
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  dsimp only [parabolicPullback]
  ring

end GlobalPhi43.MW20
