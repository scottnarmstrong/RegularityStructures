module

public import GlobalPhi43.Attachment.TreeFunctional

/-! Domain monotonicity for the actual attachment norms, before scaling. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal

namespace GlobalPhi43.Attachment

theorem cover_localTest_mono (K : ℝ → Measure ParabolicSpace) {D E : Set ParabolicSpace}
    (h : D ⊆ E) (I : Set ℝ) (α : ℝ) (G : ParabolicSpace → ParabolicSpace → ℝ) :
    localTestSeminorm K D I α G ≤ localTestSeminorm K E I α G := by
  unfold localTestSeminorm
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le x (le_iSup_of_le (h hx) le_rfl)

theorem cover_holder_mono (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace}
    (h : D ⊆ E) (α : ℝ) : scalarHolderSeminorm f D α ≤ scalarHolderSeminorm f E α := by
  unfold scalarHolderSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup_of_le x (le_iSup_of_le (h hx)
    (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))

theorem cover_XV_mono (K : ℝ → Measure ParabolicSpace) {D E : Set ParabolicSpace}
    (h : D ⊆ E) (κ : ℝ) (V : ParabolicSpace → ℝ) :
    recenteredXVSeminorm K D κ V ≤ recenteredXVSeminorm K E κ V := by
  unfold recenteredXVSeminorm
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le x (le_iSup_of_le (h hx) le_rfl)

theorem cover_scalarSup_mono (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace}
    (h : D ⊆ E) : localScalarSup f D ≤ localScalarSup f E := by
  unfold localScalarSup
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le x (le_iSup_of_le (h hx) le_rfl)

/-- All nine entries are the original source norms, with no altered test profile. -/
theorem attachmentTreeSeminorm_mono (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) {D E : Set ParabolicSpace} (h : D ⊆ E) (τ : LocalTree) :
    attachmentTreeSeminorm N κ Φ hΦ f C D τ ≤ attachmentTreeSeminorm N κ Φ hΦ f C E τ := by
  cases τ <;> simp only [attachmentTreeSeminorm]
  · exact cover_localTest_mono _ h _ _ _
  · exact cover_localTest_mono _ h _ _ _
  · exact cover_localTest_mono _ h _ _ _
  · exact cover_holder_mono _ h _
  · exact cover_holder_mono _ h _
  · exact cover_XV_mono _ h _ _
  · exact cover_localTest_mono _ h _ _ _
  · exact cover_localTest_mono _ h _ _ _
  · exact cover_localTest_mono _ h _ _ _

end GlobalPhi43.Attachment
