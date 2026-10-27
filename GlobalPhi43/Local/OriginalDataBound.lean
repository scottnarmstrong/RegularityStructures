module

public import GlobalPhi43.Local.OriginalDataStopping
public import GlobalPhi43.MW20.Setting.MWInnerCylinder

/-! The cylinder supremum, with the twelve-entry functional. -/
public noncomputable section
namespace GlobalPhi43.Local
open RegularityStructures MW20 Attachment Set
open scoped ContDiff ENNReal NNReal

theorem exists_original_data_bound {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (1 / 14)) :
    ∃ C : ℝ≥0, ∀ (Φ : ParabolicSpace → ℝ) (_hΦ : KernelProfile Φ)
      (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
      ∀ R ∈ Ioo (0 : ℝ) 1,
      supNormOn (mwInnerCylinder R) (u - J) ≤ (C : ℝ≥0∞) *
        max (ENNReal.ofReal (1 / R))
          (mwDataMaximum κ Φ (parabolicClosedNbhd mwCylinder 1) J Y Z e₁ e₂ e₃ C₁ C₂) := by
  obtain ⟨K, hK, hStop⟩ := exists_original_data_stopping_bound hκ
  refine ⟨⟨K, hK.le⟩, ?_⟩
  intro Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd R hR
  rw [← genericMWDataFunctional_eq_mwDataMaximum κ Φ hΦ]
  let F := genericMWDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂
  have hcoef : ENNReal.ofReal K = ENNReal.ofNNReal ⟨K, hK.le⟩ :=
    ENNReal.ofReal_eq_coe_nnreal hK.le
  change _ ≤ ENNReal.ofNNReal ⟨K, hK.le⟩ * max (ENNReal.ofReal (1 / R)) F
  rw [← hcoef]
  by_cases hF : F = ⊤
  · rw [hF, max_eq_right le_top, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hK))]
    exact le_top
  have hmass := hStop Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd F.toReal
    ENNReal.toReal_nonneg (le_of_eq (ENNReal.ofReal_toReal hF).symm) R hR
  have hu : ∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
      ContDiffOn ℝ ∞ u O := by
    simpa only [mwCylinder_eq_sourceCylinder] using hd.1
  have hv := remainder_continuousOn_closed u J hu hd.2.2.1.continuous.continuousOn
  unfold supNormOn
  refine iSup_le fun z => iSup_le fun hz => ?_
  have hzsource : z ∈ sourceCylinder R := by
    change (R ^ 2 < z.1 ∧ z.1 < 1) ∧ ‖z.2‖ < 1 - R at hz
    refine ⟨hz.1.1, hz.1.2, ?_⟩
    simpa only [Real.norm_eq_abs] using (pi_norm_lt_iff (sub_pos.mpr hR.2)).mp hz.2
  have hab := (abs_le_sourceSup_on hv hR.1.le hzsource).trans hmass
  rw [← ofReal_norm, Pi.sub_apply, Real.norm_eq_abs]
  apply (ENNReal.ofReal_le_ofReal hab).trans
  rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_max, ENNReal.ofReal_toReal hF]

end GlobalPhi43.Local
