module

public import GlobalPhi43.MW20.SmoothingIdentity
public import GlobalPhi43.MW20.Setting.MWNegSeminorm
public import GlobalPhi43.MW20.Setting.MWRecenteredSeminorm

/-! Identities for scalar testing seminorms, with both scale endpoints retained. -/

public section
namespace GlobalPhi43.MW20
open MeasureTheory RegularityStructures Set

private theorem mwSmooth_scaled_enorm_eq (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1) (α : ℝ) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    ENNReal.ofReal (T^(-α)) * ‖mwSmooth Φ T f x‖ₑ =
      ENNReal.ofReal (T^(-α)*|pastSmooth (mw20TestingKernel Φ hΦ T) f x|) := by
  rw [mwSmooth_eq_pastSmooth Φ hΦ hT hT1,← ofReal_norm,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _),Real.norm_eq_abs]

theorem mwNegSeminorm_eq_negativeTreeSeminorm (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (α : ℝ) (D : Set ParabolicSpace) (f : ParabolicSpace → ℝ) :
    mwNegSeminorm Φ α D f = negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D α f := by
  unfold mwNegSeminorm negativeTreeSeminorm localTestSeminorm
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => iSup_le fun x => iSup_le fun hx => ?_
    rw [mwSmooth_scaled_enorm_eq Φ hΦ hT.1 hT.2]
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le T (le_iSup_of_le hT le_rfl)))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun T => iSup_le fun hT => ?_
    rw [← mwSmooth_scaled_enorm_eq Φ hΦ hT.1 hT.2]
    exact le_iSup_of_le T (le_iSup_of_le hT (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))

theorem mwRecenteredSeminorm_eq_localTestSeminorm (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (α : ℝ) (D : Set ParabolicSpace) (F : ParabolicSpace → ParabolicSpace → ℝ) :
    mwRecenteredSeminorm Φ α D F =
      localTestSeminorm (mw20TestingKernel Φ hΦ) D (Ioo 0 1) α F := by
  unfold mwRecenteredSeminorm localTestSeminorm
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun T => iSup_congr fun hT => ?_
  change ENNReal.ofReal (T^(-α))*‖mwSmooth Φ T (F x) x‖ₑ = _
  exact mwSmooth_scaled_enorm_eq Φ hΦ hT.1 hT.2.le α (F x) x

theorem mwRecenteredSeminorm_eq_A (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (κ : ℝ) (D : Set ParabolicSpace) (Y V : ParabolicSpace → ℝ) (C₂ : ℝ) :
    mwRecenteredSeminorm Φ (-4*κ) D (fun x y => (Y y-Y x)*V y-C₂) =
      recenteredASeminorm (mw20TestingKernel Φ hΦ) D κ Y V C₂ :=
  mwRecenteredSeminorm_eq_localTestSeminorm Φ hΦ _ _ _

theorem mwRecenteredSeminorm_eq_B (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (κ : ℝ) (D : Set ParabolicSpace) (Z J : ParabolicSpace → ℝ) :
    mwRecenteredSeminorm Φ (-4*κ) D (fun x y => (Z y-Z x)*J y) =
      recenteredBSeminorm (mw20TestingKernel Φ hΦ) D κ Z J :=
  mwRecenteredSeminorm_eq_localTestSeminorm Φ hΦ _ _ _

theorem mwRecenteredSeminorm_eq_D (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (κ : ℝ) (D : Set ParabolicSpace) (Z V J : ParabolicSpace → ℝ) (C₂ : ℝ) :
    mwRecenteredSeminorm Φ (-(1/2)-5*κ) D (fun x y => (Z y-Z x)*V y-3*C₂*J y) =
      recenteredDSeminorm (mw20TestingKernel Φ hΦ) D κ Z V J C₂ :=
  mwRecenteredSeminorm_eq_localTestSeminorm Φ hΦ _ _ _

end GlobalPhi43.MW20
