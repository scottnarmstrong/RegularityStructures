module

public import GlobalPhi43.MW20.CoordinateTransport

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- XV identity with the exact open truncated-scale supremum and
source n=2 degree; the vector norm is the actual spatial supremum norm. -/
theorem recenteredXV_scaling (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) (b : ParabolicSpace)
    {ℓ : ℝ} (hℓ : 0<ℓ) (D : Set ParabolicSpace) (κ : ℝ) :
    recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D κ (parabolicPullback (ℓ^2) V b ℓ) =
      ENNReal.ofReal (ℓ^(2*(1/2-κ))) *
        ⨆ x ∈ parabolicMap b ℓ '' D, ⨆ t ∈ Ioo (0 : ℝ) ℓ,
          ENNReal.ofReal (t^(2*κ)*‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x‖) := by
  rw [← image_scale_Ioo hℓ]
  simp only [recenteredXVSeminorm,iSup_image,ENNReal.mul_iSup]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  rw [coordinateTreeTest_parabolicPullback Φ hΦ V hV b hℓ ht.1,
    norm_smul,Real.norm_eq_abs,abs_of_pos hℓ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _)]
  apply congrArg ENNReal.ofReal
  rw [Real.mul_rpow hℓ.le ht.1.le]
  have hp : ℓ^(2*(1/2-κ))*ℓ^(2*κ)=ℓ := by
    rw [← Real.rpow_add hℓ,show 2*(1/2-κ)+2*κ=1 by ring,Real.rpow_one]
  calc
    _ = ℓ*(t^(2*κ)*‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V (ℓ*t)
        (parabolicMap b ℓ x)‖) := by ring
    _ = (ℓ^(2*(1/2-κ))*ℓ^(2*κ))*(t^(2*κ)*‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V (ℓ*t)
        (parabolicMap b ℓ x)‖) := by rw [hp]
    _ = _ := by ring

end GlobalPhi43.MW20
