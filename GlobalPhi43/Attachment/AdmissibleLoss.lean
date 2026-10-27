module

public import Phi43.TheoremA.Parameters
public import GlobalPhi43.Attachment.OrderCheck

/-! Choice of an admissible loss exponent. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures.Phi43 Set

/-- The source admissibility condition; the Kappa carrier supplies the interval (0,1/16). -/
def AdmissibleLoss (η' : ℝ) (κ : Kappa) : Prop :=
  κ.1 ∉ Statements.excludedKappa ∧ κ.1 < -(1 / 2 : ℝ) - η'

/-- The existing public parameter theorem supplies the nonempty admissible set. -/
theorem exists_admissibleLoss (η' : ℝ) (hη : η' < -(1 / 2 : ℝ)) :
    ∃ κ : Kappa, AdmissibleLoss η' κ := assembly_exists_kappa η' hη

/-- A fixed choice from the target alone, before any noise space or model is introduced. -/
def selectedLoss (η' : ℝ) (hη : η' < -(1 / 2 : ℝ)) : Kappa :=
  (exists_admissibleLoss η' hη).choose

theorem selectedLoss_spec (η' : ℝ) (hη : η' < -(1 / 2 : ℝ)) :
    AdmissibleLoss η' (selectedLoss η' hη) := (exists_admissibleLoss η' hη).choose_spec

end GlobalPhi43.Attachment
