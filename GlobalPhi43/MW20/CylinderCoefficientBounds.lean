module

public import GlobalPhi43.MW20.CylinderCone
public import GlobalPhi43.MW20.ConeHolderSeminorm

/-! Spatial interior-cone geometry for the fixed-cylinder coefficient estimates. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The actual source inset cylinders are open. -/
theorem isOpen_cylinderInterior (R d : ℝ) : IsOpen (cylinderInterior R d) := by
  have ht : IsOpen {x : ParabolicSpace | R ^ 2 + d ^ 2 < x.1} :=
    isOpen_lt continuous_const continuous_fst
  have hu : IsOpen {x : ParabolicSpace | x.1 < 1} :=
    isOpen_lt continuous_fst continuous_const
  have hs : IsOpen {x : ParabolicSpace | ∀ i : Fin 3,
      -1 + R + d < x.2 i ∧ x.2 i < 1 - R - d} := by
    have hi : ∀ i : Fin 3, IsOpen {x : ParabolicSpace |
        -1 + R + d < x.2 i ∧ x.2 i < 1 - R - d} := fun i =>
      (isOpen_lt continuous_const ((continuous_apply i).comp continuous_snd)).inter
        (isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const)
    simpa only [ofPred_forall] using isOpen_iInter_of_finite hi
  exact ht.inter (hu.inter hs)

end GlobalPhi43.MW20
