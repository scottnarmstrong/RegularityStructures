module

public import GlobalPhi43.Attachment.TreeFunctional
public import GlobalPhi43.MW20.Setting.IsMWLocalData
public import GlobalPhi43.MW20.Setting.MWInnerCylinder

/-! The Moinat–Weber half-cylinder bound in terms of the local tree seminorms. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- The original nine source norms for arbitrary local-data representatives. -/
@[expose] def mwDataTreeSeminorm (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) (S : Set ParabolicSpace) (τ : LocalTree) : ℝ≥0∞ :=
  let V := fun z => J z^2-C₁
  let W := fun z => J z^3-3*C₁*J z
  let K := mw20TestingKernel Φ hΦ
  match τ with
  | .J => negativeTreeSeminorm K S (-1/2-κ.1) J
  | .V => negativeTreeSeminorm K S (-1-2*κ.1) V
  | .W => negativeTreeSeminorm K S (-3/2-3*κ.1) W
  | .Y => scalarHolderSeminorm Y S (1-2*κ.1)
  | .Z => scalarHolderSeminorm Z S (1/2-3*κ.1)
  | .XV => recenteredXVSeminorm K S κ.1 V
  | .A => recenteredASeminorm K S κ.1 Y V C₂
  | .B => recenteredBSeminorm K S κ.1 Z J
  | .D => recenteredDSeminorm K S κ.1 Z V J C₂

/-- The original twelve rooted entries on P-plus, with signed counterterms intact. -/
@[expose] def mwDataFunctional (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) : ℝ≥0∞ :=
  let S := parabolicClosedNbhd mwCylinder 1
  max (⨆ τ : LocalTree, mwDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ S τ ^ (τ.degree κ.1)⁻¹)
    (max (localScalarSup e₁ S ^ (1/3 : ℝ))
      (max (localScalarSup e₂ S ^ (1/2 : ℝ)) (localScalarSup e₃ S ^ (1/3 : ℝ))))

/-- One coefficient bounds u-minus-J for all local data on the half-cylinder
R = 1/2, using the twelve-entry tree and defect functional. -/
@[expose] def MW20HalfCylinderBound (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : ℝ≥0) : Prop :=
  ∀ (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
    IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
    ∀ z ∈ mwInnerCylinder (1/2), ENNReal.ofReal |u z-J z| ≤
      (C : ℝ≥0∞) * max 2 (mwDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂)

end GlobalPhi43.Attachment
