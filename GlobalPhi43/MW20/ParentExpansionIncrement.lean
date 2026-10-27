module

public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm

/-! The dimension-three spatial pairing bound used by the retained interpolation proofs. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The spatial affine term, in the project's max coordinate norm. -/
theorem spatialPair_abs_le (ν : Fin 3 → ℝ) (x y : ParabolicSpace) :
    |∑ i, ν i * (y.2 i - x.2 i)| ≤ 3 * ‖ν‖ * Local.pdist x y := by
  have hs : ‖y.2 - x.2‖ ≤ Local.pdist x y := by
    rw [norm_sub_rev]
    exact le_max_right _ _
  have hcoord (i : Fin 3) : |y.2 i - x.2 i| ≤ Local.pdist x y := by
    have hh : |y.2 i - x.2 i| ≤ ‖y.2 - x.2‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y.2 - x.2) i
    exact hh.trans hs
  calc
    _ ≤ ∑ i : Fin 3, |ν i * (y.2 i - x.2 i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖ν‖ * Local.pdist x y := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ν i)
        (hcoord i)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

end GlobalPhi43.MW20
