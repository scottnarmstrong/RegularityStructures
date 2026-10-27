module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Ring

/-!
# Exact first and second affine chain rules for real fields
-/

public section

namespace GlobalPhi43.MW20

/-- The total real derivative respects affine changes of variables, including
zero scales. No differentiability hypothesis is needed for this identity. -/
theorem deriv_affine_pullback (f : ℝ → ℝ) (A a c s : ℝ) :
    deriv (fun t => A * f (a + c * t)) s = A * c * deriv f (a + c * s) := by
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left c (fun t => f (a + t)) s
  simp only [deriv_comp_const_add, smul_eq_mul] at h
  rw [h]
  ring

/-- Iterating the affine chain rule gives the exact second derivative. -/
theorem second_deriv_affine_pullback (f : ℝ → ℝ) (A a c s : ℝ) :
    deriv (deriv (fun t => A * f (a + c * t))) s =
      A * c ^ 2 * deriv (deriv f) (a + c * s) := by
  have he : deriv (fun t => A * f (a + c * t)) =
      fun t => A * c * deriv f (a + c * t) := funext fun t => deriv_affine_pullback f A a c t
  rw [he, deriv_affine_pullback]
  ring

end GlobalPhi43.MW20
