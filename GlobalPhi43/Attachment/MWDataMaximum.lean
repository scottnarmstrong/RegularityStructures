module

public import GlobalPhi43.Attachment.MW20HalfCylinderBound
public import GlobalPhi43.MW20.CoordinateNormIdentity
public import GlobalPhi43.MW20.LocalPositiveHolder
public import GlobalPhi43.MW20.Setting.SupNormOn

/-! Identification of the twelve-entry maximum with the tree and defect functional. -/

@[expose] public noncomputable section
namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ENNReal

/-- The nine rooted tree norms and three defects in the bounded-defect estimate,
on the original base domain.
This definition is valid at every real loss, in particular the whole (0,1/14) range. -/
def mwDataMaximum (κ : ℝ) (Φ : ParabolicSpace → ℝ) (S : Set ParabolicSpace)
    (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) : ℝ≥0∞ :=
  max (mwNegSeminorm Φ (-(1/2)-κ) S J ^ (1/(1*(1/2-κ))))
  (max (mwNegSeminorm Φ (-1-2*κ) S (fun z => J z^2-C₁) ^ (1/(2*(1/2-κ))))
  (max (mwRecenteredSeminorm Φ (-(2*κ)) S (fun x y => (J y^2-C₁) • (y.2-x.2)) ^ (1/(2*(1/2-κ))))
  (max (parabolicHolderSeminorm (1-2*κ) S Y ^ (1/(2*(1/2-κ))))
  (max (mwNegSeminorm Φ (-(3/2)-3*κ) S (fun z => J z^3-3*C₁*J z) ^ (1/(3*(1/2-κ))))
  (max (parabolicHolderSeminorm (1/2-3*κ) S Z ^ (1/(3*(1/2-κ))))
  (max (mwRecenteredSeminorm Φ (-(4*κ)) S (fun x y => Y y*(J y^2-C₁)-C₂-Y x*(J y^2-C₁)) ^ (1/(4*(1/2-κ))))
  (max (mwRecenteredSeminorm Φ (-(4*κ)) S (fun x y => Z y*J y-Z x*J y) ^ (1/(4*(1/2-κ))))
  (max (mwRecenteredSeminorm Φ (-(1/2)-5*κ) S (fun x y => Z y*(J y^2-C₁)-3*C₂*J y-Z x*(J y^2-C₁)) ^ (1/(5*(1/2-κ))))
  (max (supNormOn S e₁ ^ (1/3:ℝ))
  (max (supNormOn S e₂ ^ (1/2:ℝ)) (supNormOn S e₃ ^ (1/3:ℝ))))))))))))

theorem localTree_iSup_eq_max (f : LocalTree → ℝ≥0∞) :
    (⨆ τ, f τ) = max (f .J) (max (f .V) (max (f .XV) (max (f .Y)
      (max (f .W) (max (f .Z) (max (f .A) (max (f .B) (f .D)))))))) := by
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    cases τ <;> simp [le_max_iff]
  · simp only [max_le_iff]
    repeat' constructor
    all_goals exact le_iSup f _

theorem localScalarSup_eq_supNormOn (f : ParabolicSpace → ℝ) (S : Set ParabolicSpace) :
    localScalarSup f S = supNormOn S f := by
  simp only [localScalarSup,supNormOn,← ofReal_norm,Real.norm_eq_abs]

theorem mwDataFunctional_eq_mwDataMaximum (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) :
    mwDataFunctional κ Φ hΦ J Y Z e₁ e₂ e₃ C₁ C₂ =
      mwDataMaximum κ Φ (parabolicClosedNbhd mwCylinder 1) J Y Z e₁ e₂ e₃ C₁ C₂ := by
  have hA : (fun x y => Y y*(J y^2-C₁)-C₂-Y x*(J y^2-C₁)) =
      (fun x y => (Y y-Y x)*(J y^2-C₁)-C₂) := by funext x y; ring
  have hB : (fun x y => Z y*J y-Z x*J y) = (fun x y => (Z y-Z x)*J y) := by funext x y; ring
  have hD : (fun x y => Z y*(J y^2-C₁)-3*C₂*J y-Z x*(J y^2-C₁)) =
      (fun x y => (Z y-Z x)*(J y^2-C₁)-3*C₂*J y) := by funext x y; ring
  rw [mwDataFunctional,localTree_iSup_eq_max]
  simp only [mwDataMaximum,mwDataTreeSeminorm,LocalTree.degree,LocalTree.leaves,
    Nat.cast_ofNat,Nat.cast_one,hA,hB,hD,← neg_mul,
    mwNegSeminorm_eq_negativeTreeSeminorm Φ hΦ,mwRecenteredSeminorm_eq_XV Φ hΦ,
    mwRecenteredSeminorm_eq_A Φ hΦ,mwRecenteredSeminorm_eq_B Φ hΦ,
    mwRecenteredSeminorm_eq_D Φ hΦ,scalarHolderSeminorm_eq_parabolicHolderSeminorm,localScalarSup_eq_supNormOn]
  norm_num only [one_div,one_mul,neg_div]
  simp only [max_assoc]

end GlobalPhi43.Attachment
