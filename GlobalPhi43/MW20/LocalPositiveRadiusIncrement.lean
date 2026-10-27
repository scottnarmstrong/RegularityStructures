module

public import GlobalPhi43.MW20.LocalPositiveExpansion
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.ParentHolderNorm

/-! Localized parent-amplitude estimates in terms of local positive-tree norms,
with the norms taken on the specified local domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_parent_radius_sum_increment_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (D : Set ParabolicSpace) (hD : IsOpen D)
    (hpos : D ⊆ parabolicClosedNbhd mwCylinder 1)
    {α β H N M c d : ℝ} (hd : 0 < d) (hγ : 1 < α + β) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hU : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d ≤ ENNReal.ofReal H)
    (hν : ∀ x ∈ D, ‖sourceAffineCoefficient v Y Z x‖ ≤ N)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * M ^ β))
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) (hne : y ≠ x) (hxy : Local.pdist x y ≤ d)
    (hvx : |v x| ≤ M) :
    |(v y + Z y) - (v x + Z x)| ≤
      H * Local.pdist x y ^ (α + β) + 3 * N * Local.pdist x y +
        3 * c * M ^ (1 + β) * Local.pdist x y ^ β := by
  have hrem := radiusAffineSeminorm_remainder_bound (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) D hD hγ hd hH hU hx hy hxy hne
  change |Local.expansion v Y Z x y -
    ∑ j, sourceAffineCoefficient v Y Z x j * (y.2 j - x.2 j)| ≤ _ at hrem
  have hlin := (spatialPair_abs_le (sourceAffineCoefficient v Y Z x) x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hν x hx) (by norm_num))
      (Local.pdist_nonneg x y))
  have hYinc := abs_sub_le_of_parabolicHolderSeminorm_le
    (mul_nonneg hc (Real.rpow_nonneg hM β)) hbudgetY (hpos hx) (hpos hy)
  have hprod := mul_le_mul hvx hYinc (abs_nonneg _) hM
  have hp : M ^ (1 + β) = M * M ^ β := by
    rw [Real.rpow_add' hM (by linarith : 1 + β ≠ 0)]
    rw [Real.rpow_one]
  have hbound : |3 * v x * (Y y - Y x)| ≤ 3 * c * M ^ (1 + β) * Local.pdist x y ^ β := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [hp]
    nlinarith only [hprod]
  calc
    _ = |(Local.expansion v Y Z x y -
        ∑ j, sourceAffineCoefficient v Y Z x j * (y.2 j - x.2 j)) +
        (∑ j, sourceAffineCoefficient v Y Z x j * (y.2 j - x.2 j)) -
          3 * v x * (Y y - Y x)| := by rw [Local.expansion_eq]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hrem hlin)) hbound)


theorem source_parent_radius_sum_holder_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (D : Set ParabolicSpace) (hD : IsOpen D)
    (hpos : D ⊆ parabolicClosedNbhd mwCylinder 1)
    {α β H N M c d : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1) (hγ : 1 < α + β) (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hU : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d ≤ ENNReal.ofReal H)
    (hν : ∀ x ∈ D, ‖sourceAffineCoefficient v Y Z x‖ ≤ N)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * M ^ β))
    (hvD : ∀ x ∈ D, |v x| ≤ M) :
    localSourceHolder (fun x => v x + Z x) β D d ≤
      d ^ α * H + 3 * c * M ^ (1 + β) + 3 * d ^ (1 - β) * N := by
  apply localSourceHolder_le_of_increment (by positivity)
  intro x hx y hy hp hpd
  have hne : y ≠ x := by
    intro he; subst y
    simp only [Local.pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self] at hp
    exact (lt_irrefl 0) hp
  have hi := source_parent_radius_sum_increment_positive v Y Z hv hY hZ D hD hpos hd hγ hβ hH hM hc
    hU hν hbudgetY hx hy hne hpd (hvD x hx)
  have hpH := mul_le_mul_of_nonneg_left
    (parent_holder_power hp hpd (show β ≤ α + β by linarith)) hH
  have hpN := mul_le_mul_of_nonneg_left
    (parent_holder_power hp hpd hβ1) (show 0 ≤ 3 * N by positivity)
  have he : α + β - β = α := by ring
  simp only [he, Real.rpow_one] at hpH hpN
  nlinarith only [hi, hpH, hpN]


theorem source_parent_radius_v_holder_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (D : Set ParabolicSpace) (hD : IsOpen D)
    (hpos : D ⊆ parabolicClosedNbhd mwCylinder 1)
    {α β H N M c d : ℝ} (hd : 0 < d) (hβ : 0 ≤ β)
    (hαβ : α ≤ β) (hα1 : α ≤ 1) (hγ : 1 < α + β) (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hU : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d ≤ ENNReal.ofReal H)
    (hν : ∀ x ∈ D, ‖sourceAffineCoefficient v Y Z x‖ ≤ N)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * M ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * M ^ (1 + α)))
    (hvD : ∀ x ∈ D, |v x| ≤ M) :
    localSourceHolder v α D d ≤ d ^ β * H + c * M ^ (1 + α) +
      3 * c * d ^ (β - α) * M ^ (1 + β) + 3 * d ^ (1 - α) * N := by
  apply localSourceHolder_le_of_increment (by positivity)
  intro x hx y hy hp hpd
  have hne : y ≠ x := by
    intro he; subst y
    simp only [Local.pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self] at hp
    exact (lt_irrefl 0) hp
  have hi := source_parent_radius_sum_increment_positive v Y Z hv hY hZ D hD hpos hd hγ hβ hH hM hc
    hU hν hbudgetY hx hy hne hpd (hvD x hx)
  have hz := abs_sub_le_of_parabolicHolderSeminorm_le
    (show 0 ≤ c * M ^ (1 + α) by positivity) hbudgetZ (hpos hx) (hpos hy)
  have hvinc : |v y - v x| ≤ |(v y + Z y) - (v x + Z x)| + |Z y - Z x| := by
    calc
      _ = |((v y + Z y) - (v x + Z x)) - (Z y - Z x)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hpoint := hvinc.trans (add_le_add hi hz)
  have hpH := mul_le_mul_of_nonneg_left
    (parent_holder_power hp hpd (show α ≤ α + β by linarith)) hH
  have hpN := mul_le_mul_of_nonneg_left
    (parent_holder_power hp hpd hα1) (show 0 ≤ 3 * N by positivity)
  have hpY := mul_le_mul_of_nonneg_left
    (parent_holder_power hp hpd hαβ) (show 0 ≤ 3 * c * M ^ (1 + β) by positivity)
  have he : α + β - α = β := by ring
  simp only [he, Real.rpow_one] at hpH hpN
  nlinarith only [hpoint, hpH, hpN, hpY]


end GlobalPhi43.MW20
