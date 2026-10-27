module

public import GlobalPhi43.Attachment.PsiProfile
public import GlobalPhi43.MW20.ReconstructionIntegrals
public import GlobalPhi43.MW20.KernelNegativeSeminorms

/-! Kernel tests as averages against the fixed actual unit kernel. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures MW20

/-- A total parameter family; positive source scales agree with the actual test. -/
def unitGermAverage (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (p : ParabolicSpace × ℝ) : ℝ :=
  ∫ w, G (p.1, p.1 + parabolicDilate p.2 w) ∂infiniteKernelMeasure Φ hΦ 1 (by norm_num)

/-- Change variables in the already-proved actual infinite-kernel scaling identity. -/
theorem infinitePastSmooth_eq_unit_average (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    infinitePastSmooth Φ hΦ T hT f x =
      ∫ w, f (x + parabolicDilate T w) ∂infiniteKernelMeasure Φ hΦ 1 (by norm_num) := by
  rw [integral_infiniteKernelMeasure Φ hΦ (by norm_num : (0 : ℝ) < 1) le_rfl]
  have h := integral_comp_parabolicDilate
    (fun y => infiniteKernel Φ hΦ T hT y * f (x + y)) hT
  simp_rw [infiniteKernel_dilate Φ hΦ hT hT₁, mul_assoc] at h
  rw [integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 5 hT.ne')) h).symm

/-- The literal source test at a positive scale equals the fixed-kernel average. -/
theorem pastSmooth_eq_unitGermAverage (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (G : ParabolicSpace × ParabolicSpace → ℝ) (x : ParabolicSpace) :
    pastSmooth (mw20TestingKernel Φ hΦ T) (fun y => G (x, y)) x =
      unitGermAverage Φ hΦ G (x, T) := by
  rw [mw20TestingKernel_pos Φ hΦ hT, reconstruction_pastSmooth_eq_density Φ hΦ hT hT₁,
    infinitePastSmooth_eq_unit_average Φ hΦ hT hT₁]
  rfl

/-- Continuous actual germ tests in base point and scale, after normalization to the unit measure. -/
theorem unitGermAverage_continuous (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) :
    Continuous (unitGermAverage Φ hΦ G) := by
  have := infiniteKernelMeasure_probability Φ hΦ (by norm_num : (0 : ℝ) < 1) le_rfl
  have hs : ∀ᵐ w ∂infiniteKernelMeasure Φ hΦ 1 (by norm_num), ‖w‖ ≤ 1 := by
    simpa using reconstruction_kernel_norm_support Φ hΦ (by norm_num : (0 : ℝ) < 1) le_rfl
  have hc : Continuous (fun p : (ParabolicSpace × ℝ) × ParabolicSpace =>
      G (p.1.1, p.1.1 + parabolicDilate p.1.2 p.2)) := by
    apply hG.comp
    unfold parabolicDilate
    fun_prop
  exact continuous_compact_measure_integral _ 1 hs _ hc

end GlobalPhi43.Attachment
