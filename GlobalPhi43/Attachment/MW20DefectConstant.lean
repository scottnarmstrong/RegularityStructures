module

public import GlobalPhi43.Attachment.MWDataMaximum
public import GlobalPhi43.MW20.TestKernelOfProfile

/-! A coefficient family for the bounded-defect estimate at a fixed kernel profile. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- The bounded-defect estimate at a fixed profile: losses in (0,1/14), radii
in (0,1), and one coefficient for all local data. The bound uses the twelve-entry maximum. -/
@[expose] def HasMW20DefectBound (Φ : ParabolicSpace → ℝ) : Prop :=
  ∀ κ ∈ Ioo (0 : ℝ) (1/14), ∃ C : ℝ≥0,
    ∀ (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ → ∀ R ∈ Ioo (0 : ℝ) 1,
      supNormOn (mwInnerCylinder R) (u-J) ≤ (C : ℝ≥0∞) *
        max (ENNReal.ofReal (1/R)) (mwDataMaximum κ Φ
          (parabolicClosedNbhd mwCylinder 1) J Y Z e₁ e₂ e₃ C₁ C₂)

theorem kappa_mem_Ioo (κ : Kappa) : (κ : ℝ) ∈ Ioo (0 : ℝ) (1/14) :=
  ⟨κ.2.1, by linarith only [κ.2.2]⟩

/-- One coefficient family selected before the regularity targets and noise spaces. -/
@[expose] def HasMW20DefectBound.constant (Φ : ParabolicSpace → ℝ) (hfull : HasMW20DefectBound Φ) :
    Kappa → ℝ≥0 :=
  fun κ => (hfull κ (kappa_mem_Ioo κ)).choose

/-- The norm identities give the physical half-cylinder bound with the same
selected coefficient. -/
theorem HasMW20DefectBound.halfCylinderBound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (hfull : HasMW20DefectBound Φ) :
    ∀ κ, MW20HalfCylinderBound κ Φ hΦ (HasMW20DefectBound.constant Φ hfull κ) := by
  intro κ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd z hz
  have hb := (hfull κ (kappa_mem_Ioo κ)).choose_spec
    u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd (1/2) (by constructor <;> norm_num)
  rw [show (1/(1/2 : ℝ)) = 2 by norm_num, ENNReal.ofReal_ofNat,
    ← mwDataFunctional_eq_mwDataMaximum κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂] at hb
  apply le_trans ?_ hb
  unfold supNormOn
  have hp : ‖(u-J) z‖ₑ ≤ ⨆ w ∈ mwInnerCylinder (1/2), ‖(u-J) w‖ₑ :=
    le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  simpa only [← ofReal_norm, Real.norm_eq_abs, Pi.sub_apply] using hp

end GlobalPhi43.Attachment
