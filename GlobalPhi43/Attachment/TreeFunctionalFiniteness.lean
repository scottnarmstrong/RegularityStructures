module

public import GlobalPhi43.Attachment.TreeFunctional
public import GlobalPhi43.Attachment.DefectPDE
public import GlobalPhi43.Attachment.SmoothNoiseDefects
public import GlobalPhi43.Attachment.OrdinaryFunctionalFiniteness
public import GlobalPhi43.Attachment.PositiveFunctionalFiniteness
public import GlobalPhi43.Attachment.RecenteredFunctionalFiniteness

/-! Everywhere finiteness of the actual attachment functional from smoothness alone. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ContDiff

/-- All nine actual seminorms are finite on compact sets for every smooth forcing.
This is qualitative and does not assume a model or a polynomial noise-growth event. -/
theorem attachmentTreeSeminorm_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) (τ : LocalTree) :
    attachmentTreeSeminorm N κ Φ hΦ f C S τ ≠ ⊤ := by
  cases τ with
  | J => exact attachment_J_ne_top N κ Φ hΦ hf C S hS
  | V => exact attachment_V_ne_top N κ Φ hΦ hf C S hS
  | W => exact attachment_W_ne_top N κ Φ hΦ hf C S hS
  | Y => exact attachment_Y_ne_top N κ Φ hΦ hf C S hS
  | Z => exact attachment_Z_ne_top N κ Φ hΦ hf C S hS
  | XV => exact attachment_XV_ne_top N κ Φ hΦ hf C S hS
  | A => exact attachment_A_ne_top N κ Φ hΦ hf C S hS
  | B => exact attachment_B_ne_top N κ Φ hΦ hf C S hS
  | D => exact attachment_D_ne_top N κ Φ hΦ hf C S hS

/-- The source functional is finite at every smooth forcing, with no model/fallback hypothesis. -/
theorem attachmentFunctional_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) : attachmentFunctional N κ Φ hΦ f C S ≠ ⊤ := by
  have ht : (⨆ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f C S τ ^ (τ.degree κ.1)⁻¹) ≠ ⊤ := by
    have hτ (τ : LocalTree) :
        attachmentTreeSeminorm N κ Φ hΦ f C S τ ^ (τ.degree κ.1)⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg
        (inv_nonneg.mpr (LocalTree.degree_pos (by linarith only [κ.2.2]) τ).le)
        (attachmentTreeSeminorm_ne_top N κ Φ hΦ hf C S hS τ)
    have hsum : (∑ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f C S τ ^
        (τ.degree κ.1)⁻¹) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun τ _ => hτ τ)
    exact ne_top_of_le_ne_top hsum (iSup_le fun τ =>
      Finset.single_le_sum (f := fun τ : LocalTree =>
        attachmentTreeSeminorm N κ Φ hΦ f C S τ ^ (τ.degree κ.1)⁻¹)
        (fun _ _ => bot_le) (Finset.mem_univ τ))
  have he (i : Fin 3) : localScalarSup (defectField N f C i) S ≠ ⊤ :=
    smoothNoiseDefectSup_ne_top N C i S hS ⟨f, hf⟩
  unfold attachmentFunctional
  exact max_ne_top ht (max_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (he 0))
    (max_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (he 1))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (he 2))))

end GlobalPhi43.Attachment
