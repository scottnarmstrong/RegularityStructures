module

public import GlobalPhi43.Attachment.GenericMWDataMaximum

/-! Parent restrictions and smallness extraction throughout the loss range. -/

public section
namespace GlobalPhi43.Attachment
open RegularityStructures Local MW20 Set
open scoped ENNReal

theorem genericMWDataTreeSeminorm_mono_domain (κ : ℝ) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (J Y Z : ParabolicSpace → ℝ) (C₁ C₂ : ℝ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (τ : LocalTree) :
    genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ D τ ≤
      genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ E τ := by
  cases τ
  all_goals simp only [genericMWDataTreeSeminorm]
  case J => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case V => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case W => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case Y => exact scalarHolderSeminorm_mono_domain _ hDE _
  case Z => exact scalarHolderSeminorm_mono_domain _ hDE _
  case A => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case B => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case D => exact localTestSeminorm_mono_domain _ hDE _ _ _
  case XV =>
    unfold recenteredXVSeminorm
    refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le x (le_iSup_of_le (hDE hx) le_rfl)

/-- A bound for the full functional pays every original unrooted tree budget
on every smaller parent domain. No finite-value conversion is used. -/
theorem genericMWDataFunctional_tree_bound (κ : ℝ) (hκ : κ < 1/2) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ)
    {D : Set ParabolicSpace} (hD : D ⊆ parabolicClosedNbhd mwCylinder 1)
    {B : ℝ≥0∞} (hB : genericMWDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ ≤ B)
    (τ : LocalTree) :
    genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ D τ ≤ B ^ (τ.degree κ) := by
  apply (ENNReal.rpow_inv_le_iff (τ.degree_pos hκ)).mp
  apply (ENNReal.rpow_le_rpow (genericMWDataTreeSeminorm_mono_domain κ Φ hΦ J Y Z C₁ C₂ hD τ)
    (inv_nonneg.mpr (τ.degree_pos hκ).le)).trans
  exact (le_iSup (fun τ => genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂
    (parabolicClosedNbhd mwCylinder 1) τ ^ (τ.degree κ)⁻¹) τ).trans ((le_max_left _ _).trans hB)

/-- The three original defect powers, restricted to a parent domain, are also paid. -/
theorem genericMWDataFunctional_defect_bounds (κ : ℝ) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ)
    {D : Set ParabolicSpace} (hD : D ⊆ parabolicClosedNbhd mwCylinder 1)
    {B : ℝ≥0∞} (hB : genericMWDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ ≤ B) :
    localScalarSup e₁ D ≤ B^(3:ℝ) ∧ localScalarSup e₂ D ≤ B^(2:ℝ) ∧
      localScalarSup e₃ D ≤ B^(3:ℝ) := by
  have hm (e : ParabolicSpace → ℝ) : localScalarSup e D ≤
      localScalarSup e (parabolicClosedNbhd mwCylinder 1) := by
    refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le x (le_iSup_of_le (hD hx) le_rfl)
  have hb := (le_max_right _ _).trans hB
  change max (_ ^ (1/3:ℝ)) (max (_ ^ (1/2:ℝ)) (_ ^ (1/3:ℝ))) ≤ B at hb
  simp only [one_div] at hb
  refine ⟨(hm e₁).trans ?_,(hm e₂).trans ?_,(hm e₃).trans ?_⟩
  · exact (ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<3)).mp ((le_max_left _ _).trans hb)
  · exact (ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<2)).mp
      ((le_max_left _ _).trans ((le_max_right _ _).trans hb))
  · exact (ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<3)).mp
      ((le_max_right _ _).trans ((le_max_right _ _).trans hb))


end GlobalPhi43.Attachment
