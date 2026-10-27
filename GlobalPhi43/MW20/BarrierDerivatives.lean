module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic

/-!
# Derivatives of the reciprocal barrier factors for Lemma 2.7
-/

public section

namespace GlobalPhi43.MW20

open Filter Topology

/-- Time factor of the cubic boundary barrier. -/
@[expose] noncomputable def inverseRoot (t : ℝ) : ℝ := (Real.sqrt t)⁻¹

/-- Its derivative is minus one half its cube. -/
theorem inverseRoot_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt inverseRoot (-(inverseRoot t) ^ 3 / 2) t := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hd := (Real.hasDerivAt_sqrt ht.ne').inv hs
  convert! hd using 1
  unfold inverseRoot
  field_simp

/-- Reciprocal of an affine function, used for each spatial face. -/
@[expose] noncomputable def reciprocalAffine (a b x : ℝ) : ℝ := (a + b * x)⁻¹

/-- First derivative of a reciprocal affine factor. -/
theorem reciprocalAffine_hasDerivAt (a b : ℝ) {x : ℝ} (hx : a + b * x ≠ 0) :
    HasDerivAt (reciprocalAffine a b) (-b / (a + b * x) ^ 2) x := by
  simpa only [reciprocalAffine, zero_add, mul_one] using!
    ((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).inv hx

/-- The second derivative of a reciprocal affine factor. -/
theorem reciprocalAffine_deriv_deriv (a b : ℝ) {x : ℝ} (hx : a + b * x ≠ 0) :
    deriv (deriv (reciprocalAffine a b)) x = 2 * b ^ 2 / (a + b * x) ^ 3 := by
  have hnear : ∀ᶠ y in 𝓝 x, a + b * y ≠ 0 := by
    have hcont : ContinuousAt (fun y : ℝ => a + b * y) x := by fun_prop
    exact hcont.eventually_ne hx
  have heq : deriv (reciprocalAffine a b) =ᶠ[𝓝 x]
      fun y => -b / (a + b * y) ^ 2 := by
    filter_upwards [hnear] with y hy
    exact (reciprocalAffine_hasDerivAt a b hy).deriv
  rw [heq.deriv_eq]
  have hbase : HasDerivAt (fun y : ℝ => a + b * y) b x := by
    simpa only [zero_add, mul_one] using! (hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)
  have hd := ((hbase.pow 2).inv (pow_ne_zero 2 hx)).const_mul (-b)
  have hval : -b * (-(2 * (a + b * x) ^ (2 - 1) * b) / ((a + b * x) ^ 2) ^ 2) =
      2 * b ^ 2 / (a + b * x) ^ 3 := by
    norm_num
    field_simp
  calc
    deriv (fun y => -b / (a + b * y) ^ 2) x =
        -b * (-(2 * (a + b * x) ^ (2 - 1) * b) / ((a + b * x) ^ 2) ^ 2) := by
      simpa only [div_eq_mul_inv] using! hd.deriv
    _ = 2 * b ^ 2 / (a + b * x) ^ 3 := hval

end GlobalPhi43.MW20
