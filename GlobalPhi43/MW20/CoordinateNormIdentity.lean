module

public import GlobalPhi43.MW20.ScalarNormIdentities
public import GlobalPhi43.MW20.KernelCoordinateSeminorm

/-! The XV integral equals the vector test, with its spatial supremum norm. -/

public section
namespace GlobalPhi43.MW20
open MeasureTheory RegularityStructures Set

theorem mwRecenteredSeminorm_eq_XV (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (κ : ℝ) (D : Set ParabolicSpace) (V : ParabolicSpace → ℝ) :
    mwRecenteredSeminorm Φ (-2*κ) D (fun x y => V y • (y.2-x.2)) =
      recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D κ V := by
  unfold mwRecenteredSeminorm recenteredXVSeminorm
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun T => iSup_congr fun hT => ?_
  unfold coordinateTreeTest
  rw [integral_mwKernel_smul_eq_integral_infiniteKernelMeasure Φ hΦ hT.1 hT.2.le,
    mw20TestingKernel_pos Φ hΦ hT.1,← ofReal_norm,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hT.1.le _)]
  congr 2
  · congr 1
    ring
  · congr 1
    funext w
    simp only [Prod.snd_add,add_sub_cancel_left]

end GlobalPhi43.MW20
