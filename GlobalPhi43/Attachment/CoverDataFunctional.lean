module

public import GlobalPhi43.Attachment.MW20HalfCylinderBound
public import GlobalPhi43.Attachment.CoverRootBudget

/-! Identification of the scaled local data with the actual cover functional. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal

namespace GlobalPhi43.Attachment

/-- No replacement lift is constructed: V/W are exactly the scaled J polynomials. -/
theorem mwDataTreeSeminorm_scaled_eq (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (b : ParabolicSpace) (l : ℝ)
    (S : Set ParabolicSpace) (τ : LocalTree) :
    mwDataTreeSeminorm κ Φ hΦ
      (parabolicPullback l (fun z => treeJ N f (spaceTimeProj z)) b l)
      (parabolicPullback 1 (fun z => treeY N f (C₁ C) (spaceTimeProj z)) b l)
      (parabolicPullback l (fun z => treeZ N f (C₁ C) (spaceTimeProj z)) b l)
      (l^2*C₁ C) (l^2*C₂ C) S τ =
        scaledAttachmentTreeSeminorm N κ Φ hΦ f C b l S τ := by
  let J := fun z => treeJ N f (spaceTimeProj z)
  have hV : (fun z => parabolicPullback l J b l z ^ 2-l^2*C₁ C) =
      parabolicPullback (l^2) (fun z => treeV N f (C₁ C) (spaceTimeProj z)) b l := by
    simpa only [J, treeV] using scaled_V_eq J (C₁ C) b l
  have hW : (fun z => parabolicPullback l J b l z ^ 3-
      3*(l^2*C₁ C)*parabolicPullback l J b l z) =
      parabolicPullback (l^3) (fun z => treeW N f (C₁ C) (spaceTimeProj z)) b l := by
    simpa only [J, treeW] using scaled_W_eq J (C₁ C) b l
  cases τ <;> dsimp only [mwDataTreeSeminorm, scaledAttachmentTreeSeminorm]
  all_goals try rw [hV]
  all_goals try rw [hW]

/-- Exact equality of all twelve entries, including the normalized defect fields. -/
theorem mwDataFunctional_scaled_eq (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (b : ParabolicSpace) (l : ℝ) :
    mwDataFunctional κ Φ hΦ
      (parabolicPullback l (fun z => treeJ N f (spaceTimeProj z)) b l)
      (parabolicPullback 1 (fun z => treeY N f (C₁ C) (spaceTimeProj z)) b l)
      (parabolicPullback l (fun z => treeZ N f (C₁ C) (spaceTimeProj z)) b l)
      (parabolicPullback (l^3) (defectField N f C 0) b l)
      (parabolicPullback (l^2) (defectField N f C 1) b l)
      (parabolicPullback (l^3) (defectField N f C 2) b l)
      (l^2*C₁ C) (l^2*C₂ C) =
      scaledAttachmentFunctional N κ Φ hΦ f C b l (parabolicClosedNbhd mwCylinder 1) := by
  unfold mwDataFunctional scaledAttachmentFunctional
  simp_rw [mwDataTreeSeminorm_scaled_eq]

end GlobalPhi43.Attachment
