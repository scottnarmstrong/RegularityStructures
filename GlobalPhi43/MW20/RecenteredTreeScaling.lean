module

public import GlobalPhi43.MW20.KernelTreeScaling

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- A retains exactly its scaled C2 subtraction and the truncated open scale. -/
theorem recenteredA_scaling (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Y V : ParabolicSpace → ℝ) (C₂ : ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0<ℓ)
    (D : Set ParabolicSpace) (κ : ℝ) :
    recenteredASeminorm (mw20TestingKernel Φ hΦ) D κ
      (parabolicPullback 1 Y b ℓ) (parabolicPullback (ℓ^2) V b ℓ) (ℓ^2*C₂) =
      ENNReal.ofReal (ℓ^(4*(1/2-κ))) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioo 0 ℓ) (-4*κ) (fun x y => (Y y-Y x)*V y-C₂) := by
  let G := fun x y => (Y y-Y x)*V y-C₂
  have he : (fun x y => (parabolicPullback 1 Y b ℓ y-parabolicPullback 1 Y b ℓ x)*
      parabolicPullback (ℓ^2) V b ℓ y-ℓ^2*C₂) =
      (fun x y => ℓ^2*G (parabolicMap b ℓ x) (parabolicMap b ℓ y)) := by
    funext x y
    dsimp only [G,parabolicPullback]
    ring
  unfold recenteredASeminorm
  rw [he,localTestSeminorm_parabolicMap Φ hΦ (ℓ^2) G b hℓ D (Ioo 0 1) (fun _ ht => ht.1),
    image_scale_Ioo hℓ,naturalAmplitude_weight hℓ]
  rw [show ((2:ℕ):ℝ)+(-4*κ)=4*(1/2-κ) by norm_num; ring]

/-- B keeps distinct Z and J, with amplitude two and degree four. -/
theorem recenteredB_scaling (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Z J : ParabolicSpace → ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0<ℓ)
    (D : Set ParabolicSpace) (κ : ℝ) :
    recenteredBSeminorm (mw20TestingKernel Φ hΦ) D κ
      (parabolicPullback ℓ Z b ℓ) (parabolicPullback ℓ J b ℓ) =
      ENNReal.ofReal (ℓ^(4*(1/2-κ))) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioo 0 ℓ) (-4*κ) (fun x y => (Z y-Z x)*J y) := by
  let G := fun x y => (Z y-Z x)*J y
  have he : (fun x y => (parabolicPullback ℓ Z b ℓ y-parabolicPullback ℓ Z b ℓ x)*
      parabolicPullback ℓ J b ℓ y) =
      (fun x y => ℓ^2*G (parabolicMap b ℓ x) (parabolicMap b ℓ y)) := by
    funext x y
    dsimp only [G,parabolicPullback]
    ring
  unfold recenteredBSeminorm
  rw [he,localTestSeminorm_parabolicMap Φ hΦ (ℓ^2) G b hℓ D (Ioo 0 1) (fun _ ht => ht.1),
    image_scale_Ioo hℓ,naturalAmplitude_weight hℓ]
  rw [show ((2:ℕ):ℝ)+(-4*κ)=4*(1/2-κ) by norm_num; ring]

/-- D scales with amplitude three and retains the entire signed 3 C2 J term. -/
theorem recenteredD_scaling (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Z V J : ParabolicSpace → ℝ) (C₂ : ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0<ℓ)
    (D : Set ParabolicSpace) (κ : ℝ) :
    recenteredDSeminorm (mw20TestingKernel Φ hΦ) D κ
      (parabolicPullback ℓ Z b ℓ) (parabolicPullback (ℓ^2) V b ℓ)
      (parabolicPullback ℓ J b ℓ) (ℓ^2*C₂) =
      ENNReal.ofReal (ℓ^(5*(1/2-κ))) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioo 0 ℓ) (-(1/2)-5*κ)
        (fun x y => (Z y-Z x)*V y-3*C₂*J y) := by
  let G := fun x y => (Z y-Z x)*V y-3*C₂*J y
  have he : (fun x y => (parabolicPullback ℓ Z b ℓ y-parabolicPullback ℓ Z b ℓ x)*
      parabolicPullback (ℓ^2) V b ℓ y-3*(ℓ^2*C₂)*parabolicPullback ℓ J b ℓ y) =
      (fun x y => ℓ^3*G (parabolicMap b ℓ x) (parabolicMap b ℓ y)) := by
    funext x y
    dsimp only [G,parabolicPullback]
    ring
  unfold recenteredDSeminorm
  rw [he,localTestSeminorm_parabolicMap Φ hΦ (ℓ^3) G b hℓ D (Ioo 0 1) (fun _ ht => ht.1),
    image_scale_Ioo hℓ,naturalAmplitude_weight hℓ]
  rw [show ((3:ℕ):ℝ)+(-(1/2)-5*κ)=5*(1/2-κ) by norm_num; ring]

end GlobalPhi43.MW20
