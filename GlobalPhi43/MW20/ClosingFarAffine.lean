module

public import GlobalPhi43.MW20.LocalPositiveHolder

public import GlobalPhi43.MW20.FarAffineScaleAlgebra
public import GlobalPhi43.MW20.ParentExpansionIncrement

/-! Far source pairs are paid by parent amplitude and the actual coefficient. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The source's far affine remainder has no uncontrolled full-norm input.
All tree powers retain the parent amplitude, and the max-norm pairing has
its explicit factor three. -/
theorem source_far_affine_remainder_positive
    (v Y Z : ParabolicSpace → ℝ) (hv : SourceCubicRegularity v)
    {r d α β γ c N : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hγ : 1 ≤ γ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α)))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1)
    {x y : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hy : y ∈ Local.cylinderInterior r d) (hdp : d ≤ Local.pdist x y)
    (hν : ‖sourceAffineCoefficient v Y Z x‖ ≤ N) :
    (d ^ γ / Local.pdist x y ^ γ) *
      |sourceExpansion v Y Z (x, y) -
        ∑ i, sourceAffineCoefficient v Y Z x i * (y.2 i - x.2 i)| ≤
      6 * sourceSup v r + 3 * d * N := by
  let M := sourceSup v r
  have hN : 0 ≤ N := (norm_nonneg _).trans hν
  have hYi := abs_sub_le_of_parabolicHolderSeminorm_le
    (by positivity : 0 ≤ c * M ^ β) hbudgetY
    (mixedInterior_subset_positive hr hd.le hx) (mixedInterior_subset_positive hr hd.le hy)
  have hZi := abs_sub_le_of_parabolicHolderSeminorm_le
    (by positivity : 0 ≤ c * M ^ (1 + α)) hbudgetZ
    (mixedInterior_subset_positive hr hd.le hx) (mixedInterior_subset_positive hr hd.le hy)
  have hu := expansion_abs_le_of_increments v Y Z x y
    (abs_le_sourceSup_of_continuousOn hv.continuous hr (mixedInterior_subset_base hd.le hx))
    (abs_le_sourceSup_of_continuousOn hv.continuous hr (mixedInterior_subset_base hd.le hy)) hYi hZi
  have hp := (spatialPair_abs_le (sourceAffineCoefficient v Y Z x) x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hν (by norm_num : (0 : ℝ) ≤ 3))
      (Local.pdist_nonneg x y))
  have hm : M ^ (1 + β) = M * M ^ β := by rw [Real.rpow_add hMpos, Real.rpow_one]
  have he : |sourceExpansion v Y Z (x, y) -
      ∑ i, sourceAffineCoefficient v Y Z x i * (y.2 i - x.2 i)| ≤
      2 * M + c * M ^ (1 + α) * Local.pdist x y ^ α +
        3 * c * M ^ (1 + β) * Local.pdist x y ^ β + 3 * N * Local.pdist x y := by
    have ht := (abs_sub (sourceExpansion v Y Z (x, y))
      (∑ i, sourceAffineCoefficient v Y Z x i * (y.2 i - x.2 i))).trans (add_le_add hu hp)
    convert ht using 1
    rw [hm]
    ring
  exact far_affine_parent_envelope hd hdp hMpos hN hα hβ hαγ hβγ hγ hc hc1 hscale he

end GlobalPhi43.MW20
