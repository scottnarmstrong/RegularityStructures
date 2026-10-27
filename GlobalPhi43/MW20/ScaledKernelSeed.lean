module

public import GlobalPhi43.MW20.KernelProfile
public import GlobalPhi43.MW20.SmoothConvolutionSeed

/-!
# The actual parabolically scaled smooth seed Φ_T
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped BoundedContinuousFunction ContDiff

/-- Parabolic dilation, as a homeomorphism for a nonzero scale. -/
@[expose] noncomputable def parabolicKernelHomeomorph (c : ℝ) (hc : c ≠ 0) :
    ParabolicSpace ≃ₜ ParabolicSpace where
  toFun := parabolicDilate c
  invFun := parabolicDilate c⁻¹
  left_inv := parabolicDilate_inv_parabolicDilate hc
  right_inv := parabolicDilate_parabolicDilate_inv hc
  continuous_toFun := by
    exact (parabolicDilateCLM c).continuous.congr (fun z => parabolicDilateCLM_apply c z)
  continuous_invFun := by
    exact (parabolicDilateCLM c⁻¹).continuous.congr (fun z => parabolicDilateCLM_apply c⁻¹ z)

@[simp] theorem parabolicKernelHomeomorph_apply (c : ℝ) (hc : c ≠ 0) (z : ParabolicSpace) :
    parabolicKernelHomeomorph c hc z = parabolicDilate c z := rfl

/-- The source scaled profile; its normalization is exactly T^(-5). -/
@[expose] noncomputable def scaledKernelProfile (Φ : ParabolicSpace → ℝ) (T : ℝ) :
    ParabolicSpace → ℝ := rescaledTestFunction Φ T 0

/-- Smoothness is inherited from the actual source profile. -/
theorem scaledKernelProfile_smooth {Φ : ParabolicSpace → ℝ} (hΦ : KernelProfile Φ) (T : ℝ) :
    ContDiff ℝ ∞ (scaledKernelProfile Φ T) :=
  contDiff_rescaledTestFunction hΦ.smooth T 0

/-- The compact support is transported by the inverse parabolic homeomorphism. -/
theorem scaledKernelProfile_compact {Φ : ParabolicSpace → ℝ} (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) : HasCompactSupport (scaledKernelProfile Φ T) := by
  have hs := hΦ.compact.comp_homeomorph (parabolicKernelHomeomorph T⁻¹ (inv_ne_zero hT.ne'))
  have hh := hs.smul_left (f := fun _ : ParabolicSpace => (T ^ 5)⁻¹)
  have heq : scaledKernelProfile Φ T = (fun _ : ParabolicSpace => (T ^ 5)⁻¹) *
      (Φ ∘ parabolicKernelHomeomorph T⁻¹ (inv_ne_zero hT.ne')) := by
    funext z
    simp only [scaledKernelProfile, rescaledTestFunction, sub_zero, Pi.mul_apply,
      Function.comp_apply, parabolicKernelHomeomorph_apply]
  rw [heq]
  exact hh

/-- The scaled source profile as an actual bounded continuous seed. -/
@[expose] noncomputable def scaledKernelSeed (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (T : ℝ) (hT : 0 < T) : ParabolicSpace →ᵇ ℝ :=
  compactSmoothSeed (scaledKernelProfile Φ T) (scaledKernelProfile_smooth hΦ T)
    (scaledKernelProfile_compact hΦ hT)

@[simp] theorem scaledKernelSeed_apply (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (T : ℝ) (hT : 0 < T) (z : ParabolicSpace) :
    scaledKernelSeed Φ hΦ T hT z = (T ^ 5)⁻¹ * Φ (parabolicDilate T⁻¹ z) := by
  simp only [scaledKernelSeed, compactSmoothSeed_apply, scaledKernelProfile,
    rescaledTestFunction, sub_zero]

end GlobalPhi43.MW20
