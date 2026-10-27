module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Exact cubic-root scaling in MW20 (4.31)
-/

public section

namespace GlobalPhi43.MW20

/-- Cubing the third-exponent factor returns the original real power,
including a zero base. -/
theorem rpow_third_cube {x : ℝ} (hx : 0 ≤ x) (p : ℝ) :
    (x ^ (p / 3)) ^ 3 = x ^ p := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- The cubic commutator scale after taking its cube root. -/
@[expose] noncomputable def cubicCommutatorScale (M H T α : ℝ) : ℝ :=
  T ^ (α / 3) * M ^ (2 / 3 : ℝ) * H ^ (1 / 3 : ℝ)

/-- The universal factor 2 absorbs the cubic commutator's printed factor 6;
the powers of T, amplitude and Hölder norm are retained exactly. -/
theorem cubic_commutator_root_bound {D M H T α : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hbound : D ≤ 6 * M ^ 2 * H * T ^ α) :
    D ^ (1 / 3 : ℝ) ≤ 2 * cubicCommutatorScale M H T α := by
  have hscale : 0 ≤ cubicCommutatorScale M H T α := by
    unfold cubicCommutatorScale
    positivity
  have hcube : (cubicCommutatorScale M H T α) ^ 3 = T ^ α * M ^ 2 * H := by
    have hm : (M ^ (2 / 3 : ℝ)) ^ 3 = M ^ 2 := by
      simpa using rpow_third_cube hM 2
    have hh : (H ^ (1 / 3 : ℝ)) ^ 3 = H := by
      simpa using rpow_third_cube hH 1
    simp only [cubicCommutatorScale, mul_pow, rpow_third_cube hT, hm, hh]
  have hroot : (D ^ (1 / 3 : ℝ)) ^ 3 = D := by
    simpa using Real.rpow_inv_natCast_pow (n := 3) hD (by norm_num)
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hD _) (by positivity : 0 ≤ 2 * cubicCommutatorScale M H T α)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hroot, mul_pow, hcube]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg M) hH) (Real.rpow_nonneg hT α)]

end GlobalPhi43.MW20
