module

public import GlobalPhi43.Attachment.MWDataMaximum

/-! The aggregate definition bridge on the full real loss range, before RS specialization. -/

@[expose] public noncomputable section
namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ENNReal

def genericMWDataTreeSeminorm (κ : ℝ) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) (S : Set ParabolicSpace) (τ : LocalTree) : ℝ≥0∞ :=
  let V := fun z => J z^2-C₁
  let W := fun z => J z^3-3*C₁*J z
  let K := mw20TestingKernel Φ hΦ
  match τ with
  | .J => negativeTreeSeminorm K S (-1/2-κ) J
  | .V => negativeTreeSeminorm K S (-1-2*κ) V
  | .W => negativeTreeSeminorm K S (-3/2-3*κ) W
  | .Y => scalarHolderSeminorm Y S (1-2*κ)
  | .Z => scalarHolderSeminorm Z S (1/2-3*κ)
  | .XV => recenteredXVSeminorm K S κ V
  | .A => recenteredASeminorm K S κ Y V C₂
  | .B => recenteredBSeminorm K S κ Z J
  | .D => recenteredDSeminorm K S κ Z V J C₂

/-- The original twelve rooted entries on P-plus, with signed counterterms intact. -/
def genericMWDataFunctional (κ : ℝ) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) : ℝ≥0∞ :=
  let S := parabolicClosedNbhd mwCylinder 1
  max (⨆ τ : LocalTree, genericMWDataTreeSeminorm κ Φ hΦ J Y Z C₁ C₂ S τ ^ (τ.degree κ)⁻¹)
    (max (localScalarSup e₁ S ^ (1/3 : ℝ))
      (max (localScalarSup e₂ S ^ (1/2 : ℝ)) (localScalarSup e₃ S ^ (1/3 : ℝ))))

theorem genericMWDataFunctional_eq_mwDataMaximum (κ : ℝ) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) :
    genericMWDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ =
      mwDataMaximum κ Φ (parabolicClosedNbhd mwCylinder 1) J Y Z e₁ e₂ e₃ C₁ C₂ := by
  have hA : (fun x y => Y y*(J y^2-C₁)-C₂-Y x*(J y^2-C₁)) =
      (fun x y => (Y y-Y x)*(J y^2-C₁)-C₂) := by funext x y; ring
  have hB : (fun x y => Z y*J y-Z x*J y) = (fun x y => (Z y-Z x)*J y) := by funext x y; ring
  have hD : (fun x y => Z y*(J y^2-C₁)-3*C₂*J y-Z x*(J y^2-C₁)) =
      (fun x y => (Z y-Z x)*(J y^2-C₁)-3*C₂*J y) := by funext x y; ring
  rw [genericMWDataFunctional,localTree_iSup_eq_max]
  simp only [mwDataMaximum,genericMWDataTreeSeminorm,LocalTree.degree,LocalTree.leaves,
    Nat.cast_ofNat,Nat.cast_one,hA,hB,hD,← neg_mul,
    mwNegSeminorm_eq_negativeTreeSeminorm Φ hΦ,mwRecenteredSeminorm_eq_XV Φ hΦ,
    mwRecenteredSeminorm_eq_A Φ hΦ,mwRecenteredSeminorm_eq_B Φ hΦ,
    mwRecenteredSeminorm_eq_D Φ hΦ,scalarHolderSeminorm_eq_parabolicHolderSeminorm,localScalarSup_eq_supNormOn]
  norm_num only [one_div,one_mul,neg_div]
  simp only [max_assoc]
end GlobalPhi43.Attachment
