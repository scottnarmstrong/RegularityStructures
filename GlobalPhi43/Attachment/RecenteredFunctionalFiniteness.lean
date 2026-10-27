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

theorem attachment_XV_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .XV ≠ ⊤ := by
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  have hV : ContDiff ℝ ∞ V := defectInput_smooth (N := N) hf C 1
  exact mw20_recenteredXV_ne_top Φ hΦ S S (fun _ h => h) hS κ.2.1.le V hV.continuous

theorem attachment_A_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .A ≠ ⊤ := by
  let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
  have hY : ContDiff ℝ ∞ Y := defectPrimitive_smooth (N := N) hf C 1
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  have hV : ContDiff ℝ ∞ V := defectInput_smooth (N := N) hf C 1
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Y p.2 - Y p.1) * V p.2 - C₂ C) :=
    (((hY.continuous.comp continuous_snd).sub (hY.continuous.comp continuous_fst)).mul
      (hV.continuous.comp continuous_snd)).sub continuous_const
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioo 0 1)
    (fun _ h => ⟨h.1, h.2.le⟩) (α := -4*κ.1)
    (by have hp := κ.2.1; linarith only [hp])
      (fun p : ParabolicSpace × ParabolicSpace => (Y p.2 - Y p.1) * V p.2 - C₂ C) hG

theorem attachment_B_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .B ≠ ⊤ := by
  let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  have hZt : ContDiff ℝ ∞ Zt := defectPrimitive_smooth (N := N) hf C 2
  let J := fun y => treeJ N f (spaceTimeProj y)
  have hJ : ContDiff ℝ ∞ J := defectPrimitive_smooth (N := N) hf C 0
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Zt p.2 - Zt p.1) * J p.2) :=
    ((hZt.continuous.comp continuous_snd).sub (hZt.continuous.comp continuous_fst)).mul
      (hJ.continuous.comp continuous_snd)
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioo 0 1)
    (fun _ h => ⟨h.1, h.2.le⟩) (α := -4*κ.1)
    (by have hp := κ.2.1; linarith only [hp])
      (fun p : ParabolicSpace × ParabolicSpace => (Zt p.2 - Zt p.1) * J p.2) hG

theorem attachment_D_ne_top (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) :
    attachmentTreeSeminorm N κ Φ hΦ f C S .D ≠ ⊤ := by
  let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  have hZt : ContDiff ℝ ∞ Zt := defectPrimitive_smooth (N := N) hf C 2
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  have hV : ContDiff ℝ ∞ V := defectInput_smooth (N := N) hf C 1
  let J := fun y => treeJ N f (spaceTimeProj y)
  have hJ : ContDiff ℝ ∞ J := defectPrimitive_smooth (N := N) hf C 0
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Zt p.2 - Zt p.1) * V p.2 - 3*C₂ C*J p.2) :=
    (((hZt.continuous.comp continuous_snd).sub (hZt.continuous.comp continuous_fst)).mul
      (hV.continuous.comp continuous_snd)).sub
        (continuous_const.mul (hJ.continuous.comp continuous_snd))
  exact mw20_localTestSeminorm_ne_top Φ hΦ S S (fun _ h => h) hS (Ioo 0 1)
    (fun _ h => ⟨h.1, h.2.le⟩) (α := -(1/2)-5*κ.1)
    (by have hp := κ.2.1; linarith only [hp])
      (fun p : ParabolicSpace × ParabolicSpace => (Zt p.2 - Zt p.1) * V p.2 - 3*C₂ C*J p.2) hG

end GlobalPhi43.Attachment
