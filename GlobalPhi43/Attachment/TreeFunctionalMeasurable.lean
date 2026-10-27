module

public import GlobalPhi43.Attachment.RecenteredFunctionalMeasurable
public import GlobalPhi43.Attachment.TreeFunctionalFiniteness

/-! Common measurable attachment functional on the full smooth-noise carrier. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped NNReal

/-- Each literal tree seminorm is a measurable observable, without an outcome restriction. -/
theorem attachmentTreeSeminorm_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (C : RenormalisationConstants) (S : Set ParabolicSpace) (τ : LocalTree) :
    Measurable (fun f : SmoothNoise => attachmentTreeSeminorm N κ Φ hΦ f.1 C S τ) := by
  cases τ with
  | J => exact smoothNoisePrimitive_test_measurable N C Φ hΦ S _ 0
  | V => exact smoothNoiseInput_test_measurable N C Φ hΦ S _ 1
  | W => exact smoothNoiseInput_test_measurable N C Φ hΦ S _ 2
  | Y => exact smoothNoisePrimitive_holder_measurable N C S _ 1
  | Z => exact smoothNoisePrimitive_holder_measurable N C S _ 2
  | XV => exact attachment_XV_measurable N κ Φ hΦ C S
  | A => exact attachment_A_measurable N κ Φ hΦ C S
  | B => exact attachment_B_measurable N κ Φ hΦ C S
  | D => exact attachment_D_measurable N κ Φ hΦ C S

/-- The entire functional is measurable on all smooth forcing functions. -/
theorem attachmentFunctional_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (C : RenormalisationConstants) (S : Set ParabolicSpace) :
    Measurable (fun f : SmoothNoise => attachmentFunctional N κ Φ hΦ f.1 C S) := by
  have ht : Measurable (fun f : SmoothNoise =>
      ⨆ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f.1 C S τ ^ (τ.degree κ.1)⁻¹) :=
    .iSup (fun τ => ENNReal.continuous_rpow_const.measurable.comp
      (attachmentTreeSeminorm_measurable N κ Φ hΦ C S τ))
  have he (i : Fin 3) (p : ℝ) : Measurable (fun f : SmoothNoise =>
      localScalarSup (defectField N f.1 C i) S ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (smoothNoiseDefectSup_measurable N C i S)
  exact ht.max ((he 0 (1/3)).max ((he 1 (1/2)).max (he 2 (1/3))))

end GlobalPhi43.Attachment
