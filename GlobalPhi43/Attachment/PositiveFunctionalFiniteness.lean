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

theorem attachment_Y_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .Y ≠ ⊤ := by
  let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
  have hY : ContDiff ℝ ∞ Y := defectPrimitive_smooth (N := N) hf C 1
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : ParabolicSpace)
  have hp := κ.2.1
  have hs := κ.2.2
  change scalarHolderSeminorm Y S (1-2*κ.1) ≠ ⊤
  exact scalarHolderSeminorm_ne_top Y hY S R hR
    (by linarith only [hp, hs]) (by linarith only [hp, hs])

theorem attachment_Z_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .Z ≠ ⊤ := by
  let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  have hZt : ContDiff ℝ ∞ Zt := defectPrimitive_smooth (N := N) hf C 2
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : ParabolicSpace)
  have hp := κ.2.1
  have hs := κ.2.2
  change scalarHolderSeminorm Zt S (1/2-3*κ.1) ≠ ⊤
  exact scalarHolderSeminorm_ne_top Zt hZt S R hR
    (by linarith only [hp, hs]) (by linarith only [hp, hs])

end GlobalPhi43.Attachment
