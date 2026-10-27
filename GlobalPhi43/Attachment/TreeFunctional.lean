module

public import GlobalPhi43.Attachment.DefectFields
public import GlobalPhi43.Local.TreeIndex
public import GlobalPhi43.MW20.CoordinateSeminorm
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ScalarSupNorm

/-! The nine-tree/three-defect functional. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20

/-- Actual source seminorms, including the vector XV test and signed recentered counterterms. -/
def attachmentTreeSeminorm (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : SpaceTime → ℝ) (C : RenormalisationConstants) (S : Set ParabolicSpace) (τ : LocalTree) : ENNReal :=
  let J := fun y => treeJ N f (spaceTimeProj y)
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  let W := fun y => treeW N f (C₁ C) (spaceTimeProj y)
  let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
  let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  let K := mw20TestingKernel Φ hΦ
  match τ with
  | .J => negativeTreeSeminorm K S (-(1/2)-κ.1) J
  | .V => negativeTreeSeminorm K S (-1-2*κ.1) V
  | .W => negativeTreeSeminorm K S (-(3/2)-3*κ.1) W
  | .Y => scalarHolderSeminorm Y S (1-2*κ.1)
  | .Z => scalarHolderSeminorm Zt S (1/2-3*κ.1)
  | .XV => recenteredXVSeminorm K S κ.1 V
  | .A => recenteredASeminorm K S κ.1 Y V (C₂ C)
  | .B => recenteredBSeminorm K S κ.1 Zt J
  | .D => recenteredDSeminorm K S κ.1 Zt V J (C₂ C)

/-- The actual source M_C; extended values are retained until finiteness is proved. -/
def attachmentFunctional (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : SpaceTime → ℝ) (C : RenormalisationConstants) (S : Set ParabolicSpace) : ENNReal :=
  max (⨆ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f C S τ ^ (τ.degree κ.1)⁻¹)
    (max (localScalarSup (defectField N f C 0) S ^ (1/3 : ℝ))
      (max (localScalarSup (defectField N f C 1) S ^ (1/2 : ℝ))
        (localScalarSup (defectField N f C 2) S ^ (1/3 : ℝ))))

end GlobalPhi43.Attachment
