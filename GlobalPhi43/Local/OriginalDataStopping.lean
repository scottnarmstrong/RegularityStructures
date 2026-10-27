module

public import GlobalPhi43.Local.AugmentedLocalInterior
public import GlobalPhi43.Local.UniformDataScale
public import GlobalPhi43.Attachment.GenericMWDataRestrictions

/-! Estimates from the original data: finite stopping with one radius paying all twelve entries. -/
public noncomputable section
namespace GlobalPhi43.Local
open RegularityStructures MW20 Attachment Set
open scoped ContDiff ENNReal

theorem exists_original_data_stopping_bound {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (1 / 14)) :
    ∃ K > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
      (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
      ∀ H : ℝ, 0 ≤ H →
      genericMWDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ ≤ ENNReal.ofReal H →
      ∀ R ∈ Ioo (0 : ℝ) 1,
      sourceSup (fun z => u z - J z) R ≤ K * max (1 / R) H := by
  obtain ⟨c, hc, hc₁, C, hC, hInterior⟩ := exists_augmented_local_interior hκ.1 hκ.2
  obtain ⟨K, hK, hIter⟩ := nine_tree_remainder_sup_iteration hκ hC hc hc₁
  refine ⟨K, hK, ?_⟩
  intro Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd H hH hData R hR
  have hκhalf : κ < 1 / 2 := by linarith [hκ.2]
  have hDef := genericMWDataFunctional_defect_bounds κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂
    (D := parabolicClosedNbhd mwCylinder 1) (Subset.refl _) hData
  rw [ENNReal.ofReal_rpow_of_nonneg hH (by norm_num : (0 : ℝ) ≤ 3),
    ENNReal.ofReal_rpow_of_nonneg hH (by norm_num : (0 : ℝ) ≤ 2)] at hDef
  simp only [Real.rpow_ofNat] at hDef
  have he₁ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₁ z| ≤ H ^ 3 :=
    fun _ hz => localScalarSup_bound _ _ (by positivity) hDef.1 hz
  have he₂ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₂ z| ≤ H ^ 2 :=
    fun _ hz => localScalarSup_bound _ _ (by positivity) hDef.2.1 hz
  have he₃ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₃ z| ≤ H ^ 3 :=
    fun _ hz => localScalarSup_bound _ _ (by positivity) hDef.2.2 hz
  have hRow : RadiusInteriorRow (fun z => u z - J z) (fun τ : LocalTree => H ^ τ.degree κ)
      (fun τ => τ.degree κ) C c (H ^ 3) (H ^ 2) (H ^ 3) := by
    intro r hr haug hM Roff hOff hRoff
    have hInv : 0 < 1 / sourceSup (fun z => u z - J z) r := by positivity
    have hGap : r + 1 / sourceSup (fun z => u z - J z) r < r + Roff := by
      have : 2 / sourceSup (fun z => u z - J z) r =
          2 * (1 / sourceSup (fun z => u z - J z) r) := by ring
      linarith
    have hrhalf : r < 1 / 2 := by linarith
    have hParent : sourceCylinder r ⊆ parabolicClosedNbhd mwCylinder 1 := by
      intro z hz
      have hz₀ := sourceCylinder_antitone (by norm_num : (0 : ℝ) ≤ 0) hr.1 hz
      have hzP : z ∈ mwCylinder := by rwa [mwCylinder_eq_sourceCylinder]
      exact ⟨z, hzP, by simp [parabolicDist]⟩
    have hTree (D : Set ParabolicSpace) (hD : D ⊆ parabolicClosedNbhd mwCylinder 1) (τ : LocalTree) :
        genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ D τ ≤
          ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ τ.degree κ) := by
      have ht := genericMWDataFunctional_tree_bound κ hκhalf Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ hD hData τ
      rw [ENNReal.ofReal_rpow_of_nonneg hH (τ.degree_pos hκhalf).le] at ht
      exact ht.trans (ENNReal.ofReal_le_ofReal (haug.1 τ))
    have hi := hInterior Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd r (r + Roff) c (H ^ 3) (H ^ 2) (H ^ 3)
      hr.1 hrhalf hc.le le_rfl hM hGap hRoff.le (by positivity) (by positivity) (by positivity)
      haug.2 he₁ he₂ he₃
      (by
        have ht := hTree (parabolicClosedNbhd mwCylinder 1) (Subset.refl _) .Y
        have hd : LocalTree.degree κ .Y = 1 - 2 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, scalarHolderSeminorm_eq_parabolicHolderSeminorm, hd] using ht)
      (by
        have ht := hTree (parabolicClosedNbhd mwCylinder 1) (Subset.refl _) .Z
        have hd : LocalTree.degree κ .Z = 1 + (1 / 2 - 3 * κ) := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, scalarHolderSeminorm_eq_parabolicHolderSeminorm, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .J
        have hd : LocalTree.degree κ .J = 1 / 2 - κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd, neg_div] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .B
        have hd : LocalTree.degree κ .B = 2 - 4 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .A
        have hd : LocalTree.degree κ .A = 2 - 4 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .V
        have hd : LocalTree.degree κ .V = 1 - 2 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .XV
        have hd : LocalTree.degree κ .XV = 1 - 2 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .D
        have hd : LocalTree.degree κ .D = 5 / 2 - 5 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd] using ht)
      (by
        have ht := hTree (sourceCylinder r) hParent .W
        have hd : LocalTree.degree κ .W = 3 / 2 - 3 * κ := by
          norm_num [LocalTree.degree, LocalTree.leaves]
          ring
        simpa only [genericMWDataTreeSeminorm, ← sourceKernelFamily_eq_mw20TestingKernel, hd, neg_div] using ht)
    convert hi using 1
    congr 2
    ring
  have hu : ∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
      ContDiffOn ℝ ∞ u O := by
    simpa only [mwCylinder_eq_sourceCylinder] using hd.1
  have hb := hIter u J hu hd.2.2.1 (fun τ => H ^ τ.degree κ)
    (fun τ => Real.rpow_nonneg hH _) (H ^ 3) (H ^ 2) (H ^ 3)
    (by positivity) (by positivity) (by positivity) hRow R hR
  exact hb.trans (mul_le_mul_of_nonneg_left (max_le_max_left _
    (uniform_augmented_data_scale_le hH hκhalf)) hK.le)

end GlobalPhi43.Local
