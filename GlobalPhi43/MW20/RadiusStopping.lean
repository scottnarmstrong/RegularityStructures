module

public import GlobalPhi43.MW20.RadiusTermination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The smallness-failure branch of the source radius iteration

For source homogeneities `pτ = nτ (1/2 - ε) > 0`, failure of the contradiction
hypothesis gives a tree controlling the current mass. This is only the
ordinary-tree stopping branch. The added defect tests belong to the local
adapter, not to this MW20 port.
-/

public section

namespace GlobalPhi43.MW20

/-- Failure of the source contradiction hypothesis exposes a controlling tree.
The same smallness constant `c` appears on both sides of the implication. -/
theorem exists_tree_bound_of_not_small {I : Type*} (B p : I → ℝ) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hB : ∀ i, 0 ≤ B i) (hp : ∀ i, 0 < p i)
    (hfail : ¬ ∀ i, B i ≤ c * M ^ p i) :
    ∃ i, M < (B i / c) ^ (p i)⁻¹ := by
  push Not at hfail
  obtain ⟨i, hi⟩ := hfail
  refine ⟨i, (Real.lt_rpow_inv_iff_of_pos hM (div_nonneg (hB i) hc.le) (hp i)).2 ?_⟩
  exact (lt_div_iff₀ hc).2 (by nlinarith)

/-- Any simultaneous majorant of the displayed tree contributions controls the
mass at a stopping radius. No new allowance or enlarged smallness constant enters. -/
theorem mass_bound_of_not_small {I : Type*} (B p : I → ℝ) {M c A : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hB : ∀ i, 0 ≤ B i) (hp : ∀ i, 0 < p i)
    (hA : ∀ i, (B i / c) ^ (p i)⁻¹ ≤ A)
    (hfail : ¬ ∀ i, B i ≤ c * M ^ p i) : M ≤ A := by
  obtain ⟨i, hi⟩ := exists_tree_bound_of_not_small B p hM hc hB hp hfail
  exact hi.le.trans (hA i)

end GlobalPhi43.MW20
