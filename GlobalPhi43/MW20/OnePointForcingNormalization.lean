module

public import GlobalPhi43.Local.ScaleNormalization
public import Mathlib.Algebra.BigOperators.Field

/-! Exact forcing normalization at R=eta*L and T=eta^2*L. -/

public section

namespace GlobalPhi43.MW20

open scoped BigOperators

/-- The forcing term keeps its exact eta exponent after multiplication by T². -/
theorem one_point_forcing_normalization_term {η L γ a : ℝ}
    (hη : 0 < η) (hL : 0 < L) :
    (η * L) ^ (-γ) * L ^ 2 * ((η ^ 2 * L) ^ a * L ^ (γ - a)) =
      (η ^ 2 * L) ^ 2 * η ^ (2 * a - 4 - γ) := by
  have hT : 0 < η ^ 2 * L := mul_pos (sq_pos_of_pos hη) hL
  have htp : (η ^ 2 * L) ^ (2 : ℕ) * (η ^ 2 * L) ^ (a - 2) = (η ^ 2 * L) ^ a := by
    rw [← Real.rpow_two, ← Real.rpow_add hT]
    congr 1
    ring
  have hlp : L ^ (2 : ℕ) * L ^ (γ - a) = L ^ (γ + 2 - a) := by
    rw [← Real.rpow_two, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (η * L) ^ (-γ) * L ^ (γ + 2 - a) * (η ^ 2 * L) ^ a := by rw [← hlp]; ring
    _ = (η ^ 2 * L) ^ 2 *
        ((η * L) ^ (-γ) * L ^ (γ + 2 - a) * (η ^ 2 * L) ^ (a - 2)) := by rw [← htp]; ring
    _ = _ := by rw [GlobalPhi43.Local.normalized_forcing_power hη hL]

/-- An actual one-point T² bound supplies the normalized forcing term.
This is scale algebra; it does not assume or assert a caloric estimate. -/
theorem one_point_forcing_normalization {I : Type*} (A : Finset I) (β : I → ℝ)
    {η L γ Q N : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hq : (η ^ 2 * L) ^ 2 * Q ≤
      N * ∑ i ∈ A, (η ^ 2 * L) ^ (β i) * L ^ (γ - β i)) :
    (η * L) ^ (-γ) * L ^ 2 * Q ≤ N * ∑ i ∈ A, η ^ (2 * β i - 4 - γ) := by
  have hT : 0 < η ^ 2 * L := mul_pos (sq_pos_of_pos hη) hL
  have hw := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (Real.rpow_nonneg (mul_pos hη hL).le (-γ)) (sq_nonneg L))
  have he : ((η * L) ^ (-γ) * L ^ 2) *
      (∑ i ∈ A, (η ^ 2 * L) ^ (β i) * L ^ (γ - β i)) =
      (η ^ 2 * L) ^ 2 * (∑ i ∈ A, η ^ (2 * β i - 4 - γ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact one_point_forcing_normalization_term hη hL
  have hout : (η ^ 2 * L) ^ 2 * ((η * L) ^ (-γ) * L ^ 2 * Q) ≤
      (η ^ 2 * L) ^ 2 * (N * ∑ i ∈ A, η ^ (2 * β i - 4 - γ)) := by
    calc
      _ = ((η * L) ^ (-γ) * L ^ 2) * ((η ^ 2 * L) ^ 2 * Q) := by ring
      _ ≤ ((η * L) ^ (-γ) * L ^ 2) *
          (N * ∑ i ∈ A, (η ^ 2 * L) ^ (β i) * L ^ (γ - β i)) := hw
      _ = _ := by rw [mul_left_comm _ N, he]; ring
  exact le_of_mul_le_mul_left hout (sq_pos_of_pos hT)

end GlobalPhi43.MW20
