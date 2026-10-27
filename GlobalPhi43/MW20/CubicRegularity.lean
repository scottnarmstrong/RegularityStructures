module

public import GlobalPhi43.MW20.BarrierBoundary

/-!
# The local regularity required by the source maximum principle

Only continuity is required on the initial and spatial boundary faces.
C² germs are used at positive-time spatial interior points through time one.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The regularity of a classical source solution. This is weaker than the
standing smoothness convention and places no condition outside the closed cylinder. -/
structure SourceCubicRegularity (u : ParabolicSpace → ℝ) : Prop where
  continuous : ContinuousOn u sourceClosedCylinder
  twice : ∀ z : ParabolicSpace, 0 < z.1 → z.1 ≤ 1 →
    (∀ i, -1 < z.2 i ∧ z.2 i < 1) → ContDiffAt ℝ 2 u z

/-- Globally C² fields in particular satisfy the local source regularity. -/
theorem sourceCubicRegularity_of_contDiff {u : ParabolicSpace → ℝ} (hu : ContDiff ℝ 2 u) :
    SourceCubicRegularity u :=
  ⟨hu.continuous.continuousOn, fun _ _ _ _ => hu.contDiffAt⟩

/-- Negation preserves the exact local regularity. -/
theorem SourceCubicRegularity.neg {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u) :
    SourceCubicRegularity (fun z => -u z) :=
  ⟨hu.continuous.neg, fun z ht hT hx => (hu.twice z ht hT hx).neg⟩

end GlobalPhi43.MW20
