module

public import Phi43.Reconstruction.DuhamelPrinciple

/-! Scalar multiplication of the actual torus derivative jets. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.PDE

/-- Multiplication by a fixed scalar preserves the torus derivative identity. -/
theorem attachment_hasTorusDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)} (hg : HasTorusDeriv g Dg) (c : ℝ) :
    HasTorusDeriv (c • g) (c • Dg) := by
  have h := hg.compLeft (c • ContinuousLinearMap.id ℝ E)
  convert h using 1
  · ext x
    rfl
  · ext x i
    rfl

/-- Scalar multiplication commutes with the genuine three-coordinate torus Laplacian. -/
theorem attachment_torusLap_smul (c : ℝ) (D2g : C(Torus3, Fin 3 → Fin 3 → ℝ)) :
    torusLap (c • D2g) = c • torusLap D2g := by
  ext x
  simp only [torusLap_apply, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  exact (Finset.mul_sum ..).symm

end GlobalPhi43.Attachment
