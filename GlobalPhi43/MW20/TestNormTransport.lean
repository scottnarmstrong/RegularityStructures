module

public import GlobalPhi43.MW20.SmoothingTransport
public import GlobalPhi43.MW20.KernelNegativeSeminorms

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal

/-- Exact extended testing-norm transport with the test-scale set displayed.
The scale image is essential for negative/recentered truncations. -/
theorem localTestSeminorm_parabolicMap (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (a : ℝ) (G : ParabolicSpace → ParabolicSpace → ℝ) (b : ParabolicSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (D : Set ParabolicSpace) (I : Set ℝ)
    (hI : I ⊆ Ioi 0) (α : ℝ) :
    localTestSeminorm (mw20TestingKernel Φ hΦ) D I α
        (fun x y => a*G (parabolicMap b ℓ x) (parabolicMap b ℓ y)) =
      ENNReal.ofReal (|a| * ℓ^α) *
        localTestSeminorm (mw20TestingKernel Φ hΦ) (parabolicMap b ℓ '' D)
          ((fun t => ℓ*t) '' I) α G := by
  simp only [localTestSeminorm,iSup_image,ENNReal.mul_iSup]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  have ht0 : 0<t := hI ht
  rw [mw20TestingKernel_pos Φ hΦ ht0,
    mw20TestingKernel_pos Φ hΦ (mul_pos hℓ ht0),
    pastSmooth_infinite_eq_density_all Φ hΦ ht0,
    pastSmooth_infinite_eq_density_all Φ hΦ (mul_pos hℓ ht0)]
  have he : (fun y => a*G (parabolicMap b ℓ x) (parabolicMap b ℓ y)) =
      parabolicPullback a (G (parabolicMap b ℓ x)) b ℓ := rfl
  rw [he,infinitePastSmooth_parabolicPullback Φ hΦ a _ b hℓ ht0]
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg a) (Real.rpow_nonneg hℓ.le _))]
  apply congrArg ENNReal.ofReal
  rw [abs_mul,Real.mul_rpow hℓ.le ht0.le]
  have hp : ℓ^α*ℓ^(-α) = 1 := by
    rw [← Real.rpow_add hℓ,add_neg_cancel,Real.rpow_zero]
  calc
    _ = |a| * 1*(t^(-α)*|infinitePastSmooth Φ hΦ (ℓ*t) (mul_pos hℓ ht0)
        (G (parabolicMap b ℓ x)) (parabolicMap b ℓ x)|) := by ring
    _ = |a| * (ℓ^α*ℓ^(-α))*(t^(-α)*|infinitePastSmooth Φ hΦ (ℓ*t) (mul_pos hℓ ht0)
        (G (parabolicMap b ℓ x)) (parabolicMap b ℓ x)|) := by rw [hp]
    _ = _ := by ring

/-- The ordinary closed endpoint scales exactly, rather than being discarded. -/
theorem image_scale_Ioc {ℓ : ℝ} (hℓ : 0<ℓ) :
    (fun t : ℝ => ℓ*t) '' Ioc 0 1 = Ioc 0 ℓ := by
  ext t
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨mul_pos hℓ hs.1,by nlinarith [hs.2]⟩
  · intro ht
    refine ⟨t/ℓ,⟨div_pos ht.1 hℓ,(div_le_one hℓ).mpr ht.2⟩,?_⟩
    field_simp

/-- The recentered open endpoint remains open at the transported scale. -/
theorem image_scale_Ioo {ℓ : ℝ} (hℓ : 0<ℓ) :
    (fun t : ℝ => ℓ*t) '' Ioo 0 1 = Ioo 0 ℓ := by
  ext t
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨mul_pos hℓ hs.1,by nlinarith [hs.2]⟩
  · intro ht
    refine ⟨t/ℓ,⟨div_pos ht.1 hℓ,(div_lt_one hℓ).mpr ht.2⟩,?_⟩
    field_simp

end GlobalPhi43.MW20
