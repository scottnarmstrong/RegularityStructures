module

public import GlobalPhi43.MW20.SourceTreeRadius
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Uniform constant scope in the source radius bound

The constant is chosen before the field and the numerical tree seminorms.
Its only parameters are the fixed local-row constant, the fixed smallness
constant, and the finite family of source exponents.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Extract the fixed smallness constant from the finite tree maximum. -/
theorem treeRadiusMajorant_scale {I : Type*} [Fintype I] [Nonempty I]
    (B p : I → ℝ) {c : ℝ} (hc : 0 < c) (hB : ∀ i, 0 ≤ B i) :
    treeRadiusMajorant B p c ≤
      treeRadiusMajorant (fun _ : I => 1) p c * treeRadiusMajorant B p 1 := by
  apply Finset.sup'_le
  intro i _
  have h1 := tree_contribution_le_majorant (fun _ : I => 1) p c i
  have h2 := tree_contribution_le_majorant B p 1 i
  have heq : (B i / c) ^ (p i)⁻¹ =
      (1 / c) ^ (p i)⁻¹ * (B i / 1) ^ (p i)⁻¹ := by
    rw [div_one, Real.div_rpow (hB i) hc.le, Real.div_rpow zero_le_one hc.le,
      Real.one_rpow, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [heq]
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (div_nonneg (hB i) zero_le_one) _)
    (treeRadiusMajorant_nonneg (fun _ : I => 1) p hc (fun _ => zero_le_one))


end GlobalPhi43.MW20
