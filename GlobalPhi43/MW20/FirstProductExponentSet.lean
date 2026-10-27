module

public import GlobalPhi43.MW20.FirstProductCoherence

/-!
# Finite exponent-set reduction for the first MW20 product

The two J terms have the same testing exponent. They must be combined before
applying Theorem 2.8, whose index is a set of real exponents. The larger spatial power
is reduced on the actual radius R, retaining R^(4κ) in its coefficient. No
positive constant is added when a tree seminorm vanishes.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory

/-- A repeated testing exponent can be merged on a bounded spatial range. -/
theorem merge_repeated_test_exponent {d R t a₁ a₂ b a₃ c C₁ C₂ C₃ : ℝ}
    (hd : 0 < d) (hdR : d ≤ R) (ht : 0 ≤ t) (ha : a₂ ≤ a₁) (hC : 0 ≤ C₁) :
    C₁ * d ^ a₁ * t ^ b + C₂ * d ^ a₂ * t ^ b + C₃ * d ^ a₃ * t ^ c ≤
      (C₁ * R ^ (a₁ - a₂) + C₂) * d ^ a₂ * t ^ b + C₃ * d ^ a₃ * t ^ c := by
  have hp : d ^ a₁ ≤ R ^ (a₁ - a₂) * d ^ a₂ := by
    calc
      d ^ a₁ = d ^ (a₁ - a₂) * d ^ a₂ := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      _ ≤ R ^ (a₁ - a₂) * d ^ a₂ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd.le hdR (sub_nonneg.mpr ha))
          (Real.rpow_nonneg hd.le _)
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (Real.rpow_nonneg ht b)
  nlinarith only [hmain]

/-- The exponent set is admissible for the source reconstruction theorem. -/
theorem firstProduct_exponents_admissible {κ : ℝ} (_hκ : 0 ≤ κ) (hsmall : κ < 1 / 14) :
    0 < (1 / 2 : ℝ) - 7 * κ ∧
      ∀ β ∈ ({-(1 / 2 : ℝ) - κ, -4 * κ} : Finset ℝ), β ≤ 1 / 2 - 7 * κ := by
  constructor
  · linarith
  · intro β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with h | h <;> rw [h] <;> linarith

end GlobalPhi43.MW20
