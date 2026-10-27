module

public import GlobalPhi43.Attachment.TreeFunctional
public import GlobalPhi43.Attachment.DefectPDE
public import GlobalPhi43.MW20.KernelNegativeFiniteness
public import GlobalPhi43.MW20.KernelCoordinateFiniteness
public import GlobalPhi43.MW20.ScalarHolderFiniteness

/-! Qualitative source finiteness on every smooth forcing, without a model or growth event. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ContDiff

theorem attachment_J_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .J ≠ ⊤ := by
  let J := fun y => treeJ N f (spaceTimeProj y)
  have hJ : ContDiff ℝ ∞ J := defectPrimitive_smooth (N := N) hf C 0
  change localTestSeminorm (mw20TestingKernel Φ hΦ) S (Ioc 0 1) (-(1/2)-κ.1) (fun _ => J) ≠ ⊤
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioc 0 1) (fun _ h => h)
    (by have hp := κ.2.1; linarith only [hp]) (fun p => J p.2) (hJ.continuous.comp continuous_snd)

theorem attachment_V_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .V ≠ ⊤ := by
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  have hV : ContDiff ℝ ∞ V := defectInput_smooth (N := N) hf C 1
  change localTestSeminorm (mw20TestingKernel Φ hΦ) S (Ioc 0 1) (-1-2*κ.1) (fun _ => V) ≠ ⊤
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioc 0 1) (fun _ h => h)
    (by have hp := κ.2.1; linarith only [hp]) (fun p => V p.2) (hV.continuous.comp continuous_snd)

theorem attachment_W_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .W ≠ ⊤ := by
  let W := fun y => treeW N f (C₁ C) (spaceTimeProj y)
  have hW : ContDiff ℝ ∞ W := defectInput_smooth (N := N) hf C 2
  change localTestSeminorm (mw20TestingKernel Φ hΦ) S (Ioc 0 1) (-(3/2)-3*κ.1) (fun _ => W) ≠ ⊤
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioc 0 1) (fun _ h => h)
    (by have hp := κ.2.1; linarith only [hp]) (fun p => W p.2) (hW.continuous.comp continuous_snd)

end GlobalPhi43.Attachment
