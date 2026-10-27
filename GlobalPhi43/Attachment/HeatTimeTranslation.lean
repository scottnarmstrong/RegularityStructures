module

public import GlobalPhi43.Attachment.SliceDifferencePDE

/-! Translation and the actual classical heat operator on smooth periodic fields. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Inhomogeneity RegularityStructures.Potential
open scoped ContDiff

def attachmentHeatOperator (F : ParabolicSpace → ℝ) : ParabolicSpace → ℝ :=
  fun z => ddv 0 F z - ∑ j : Fin 3, ddv j.succ (ddv j.succ F) z

theorem attachmentHeatOperator_perSmooth {F : ParabolicSpace → ℝ} (hF : PerSmooth F) :
    PerSmooth (attachmentHeatOperator F) where
  smooth := (hF.ddv 0).smooth.sub (ContDiff.sum fun (j : Fin 3) _ => ((hF.ddv j.succ).ddv j.succ).smooth)
  periodic z c hc := by
    change ddv 0 F (z.1,z.2+c) - ∑ j : Fin 3, ddv j.succ (ddv j.succ F) (z.1,z.2+c) = _
    rw [(hF.ddv 0).periodic z c hc]
    congr 1
    exact Finset.sum_congr rfl fun (j : Fin 3) _ => ((hF.ddv j.succ).ddv j.succ).periodic z c hc

theorem attachment_ddv_translate (F : ParabolicSpace → ℝ) (v : ParabolicSpace) (j : Fin 4) :
    ddv j (fun z => F (v+z)) = fun z => ddv j F (v+z) := by
  funext z
  simp only [ddv, fderiv_comp_add_left]

end GlobalPhi43.Attachment
