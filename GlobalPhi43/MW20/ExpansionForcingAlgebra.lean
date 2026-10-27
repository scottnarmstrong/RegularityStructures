module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Complete signed forcing combination for the small-scale expansion
-/

public section

namespace GlobalPhi43.MW20

/-- Keep the second product and its counterterm together before estimating. -/
theorem expansion_forcing_abs {heat cubic product mixed rec counter : ℝ}
    (heq : heat = -cubic - 3 * product - 3 * mixed - 3 * rec - 9 * counter) :
    |heat| ≤ |cubic| + 3 * |product| + 3 * |mixed| + 3 * |rec + 3 * counter| := by
  have he : heat = -cubic - 3 * product - 3 * mixed - 3 * (rec + 3 * counter) := by
    linarith only [heq]
  rw [he]
  have h₁ := abs_sub (-cubic) (3 * product)
  have h₂ := abs_sub (-cubic - 3 * product) (3 * mixed)
  have h₃ := abs_sub (-cubic - 3 * product - 3 * mixed) (3 * (rec + 3 * counter))
  simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h₁ h₂ h₃
  linarith only [h₁, h₂, h₃]

end GlobalPhi43.MW20
