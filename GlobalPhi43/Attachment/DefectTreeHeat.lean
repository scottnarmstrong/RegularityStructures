module

public import GlobalPhi43.Attachment.DefectPDE
public import GlobalPhi43.MW20.Setting.HeatOperator

/-! Primitive equations in the MW heat-operator convention. -/

public noncomputable section

open RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Inhomogeneity

namespace GlobalPhi43.Attachment

/-- The operator and the coordinate derivatives agree exactly. -/
theorem heatOperator_eq_ddv (g : ParabolicSpace → ℝ) (z : ParabolicSpace) :
    heatOperator g z = ddv 0 g z - ∑ j : Fin 3, ddv j.succ (ddv j.succ g) z := by
  unfold heatOperator ddv
  simp only [Datum.stBasis_zero, Datum.stBasis_succ]

/-- All three actual J/Y/Z equations, with the signed actual defect fields.
This is unconditional for smooth forcing and arbitrary counterterms. -/
theorem heatOperator_defectPrimitive {N : ℕ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (i : Fin 3) (z : ParabolicSpace) :
    heatOperator (fun w => defectPrimitive N f C i (spaceTimeProj w)) z =
      defectInput N f C i z + defectField N f C i z := by
  rw [heatOperator_eq_ddv]
  exact defect_pde hf C i z

end GlobalPhi43.Attachment
