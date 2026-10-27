module

public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.MW20.RadiusMaximumStep

/-!
# Source tree stopping in the actual cylinder radius estimate

The displayed maximum is over the finite source tree family, with exponents
`pτ = nτ (1/2 - ε)`. Here the positive exponents and the nonnegative numerical
tree seminorms are parameters. The estimate (4.33) under the source smallness
hypothesis remains the explicit analytic input.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The finite maximum of the tree contributions exposed by failure of (4.1). -/
@[expose] noncomputable def treeRadiusMajorant {I : Type*} [Fintype I] [Nonempty I]
    (B p : I → ℝ) (c : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (B i / c) ^ (p i)⁻¹)

/-- Each stopping contribution lies below the same finite maximum. -/
theorem tree_contribution_le_majorant {I : Type*} [Fintype I] [Nonempty I]
    (B p : I → ℝ) (c : ℝ) (i : I) : (B i / c) ^ (p i)⁻¹ ≤ treeRadiusMajorant B p c := by
  exact Finset.le_sup' (f := fun i => (B i / c) ^ (p i)⁻¹) (Finset.mem_univ i)

/-- The majorant is nonnegative for nonnegative tree seminorms and positive c. -/
theorem treeRadiusMajorant_nonneg {I : Type*} [Fintype I] [Nonempty I]
    (B p : I → ℝ) {c : ℝ} (hc : 0 < c) (hB : ∀ i, 0 ≤ B i) :
    0 ≤ treeRadiusMajorant B p c := by
  let i : I := Classical.choice inferInstance
  exact (Real.rpow_nonneg (div_nonneg (hB i) hc.le) _).trans
    (tree_contribution_le_majorant B p c i)

end GlobalPhi43.MW20
