module

public import GlobalPhi43.Attachment.Realisation

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43

/-- The scalar A realisation is the literal YV increment with its C2 subtraction. -/
theorem source_A_eq (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (x y : ParabolicSpace) :
    hairerTreeField N (fun _ : Unit => f) (C₁ C) (C₂ C) (spaceTimeProj x) ()
        .iPsiSqPsiSq (spaceTimeProj y) =
      (treeY N f (C₁ C) (spaceTimeProj y)-treeY N f (C₁ C) (spaceTimeProj x)) *
        treeV N f (C₁ C) (spaceTimeProj y)-C₂ C := by
  change hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
    (treeV N f (C₁ C)) * treeV N f (C₁ C) (spaceTimeProj y)-C₂ C = _
  rw [pairing_treeV hf]

/-- The scalar B realisation retains the distinct J factor. -/
theorem source_B_eq (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (x y : ParabolicSpace) :
    hairerTreeField N (fun _ : Unit => f) (C₁ C) (C₂ C) (spaceTimeProj x) ()
        .iPsiCubePsi (spaceTimeProj y) =
      (treeZ N f (C₁ C) (spaceTimeProj y)-treeZ N f (C₁ C) (spaceTimeProj x)) *
        treeJ N f (spaceTimeProj y) := by
  change hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
    (treeW N f (C₁ C)) * treeJ N f (spaceTimeProj y) = _
  rw [pairing_treeW hf]

/-- The scalar D realisation retains the full signed 3 C2 J counterterm. -/
theorem source_D_eq (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (x y : ParabolicSpace) :
    hairerTreeField N (fun _ : Unit => f) (C₁ C) (C₂ C) (spaceTimeProj x) ()
        .iPsiCubePsiSq (spaceTimeProj y) =
      (treeZ N f (C₁ C) (spaceTimeProj y)-treeZ N f (C₁ C) (spaceTimeProj x)) *
        treeV N f (C₁ C) (spaceTimeProj y)-3*C₂ C*treeJ N f (spaceTimeProj y) := by
  change hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
    (treeW N f (C₁ C)) * treeV N f (C₁ C) (spaceTimeProj y)-
      3*C₂ C*treeJ N f (spaceTimeProj y) = _
  rw [pairing_treeW hf]

end GlobalPhi43.Attachment
