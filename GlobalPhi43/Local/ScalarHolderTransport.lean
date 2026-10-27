module

public import GlobalPhi43.Local.ParabolicTransport
public import GlobalPhi43.MW20.ScalarHolderSeminorm

public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

/-- Pair-based positive seminorm transport has no test-scale truncation. -/
theorem scalarHolderSeminorm_parabolicPullback (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : Set ParabolicSpace) (α : ℝ) :
    scalarHolderSeminorm (parabolicPullback a f b ℓ) D α =
      ENNReal.ofReal (|a| * ℓ^α) * scalarHolderSeminorm f (parabolicMap b ℓ '' D) α := by
  have hinj : Function.Injective (parabolicMap b ℓ) :=
    (parabolicTransport b ℓ hℓ.ne').injective
  simp only [scalarHolderSeminorm,iSup_image,hinj.ne_iff,ENNReal.mul_iSup]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  apply iSup_congr
  intro y
  apply iSup_congr
  intro hy
  apply iSup_congr
  intro hne
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg a) (Real.rpow_nonneg hℓ.le _))]
  apply congrArg ENNReal.ofReal
  have hd := pdist_pos_of_ne hne
  rw [parabolicPullback,parabolicPullback,← mul_sub,abs_mul,pdist_parabolicMap b hℓ,
    Real.mul_rpow hℓ.le hd.le]
  field_simp

end GlobalPhi43.Local
