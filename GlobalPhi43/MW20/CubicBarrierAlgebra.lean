module

public import Mathlib.Tactic

/-!
# Cubic supersolution algebra for the boundary barrier
-/

public section

namespace GlobalPhi43.MW20

/-- Nonnegative cubes are superadditive. -/
theorem cube_add_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 3 + b ^ 3 ≤ (a + b) ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg a) hb, mul_nonneg ha (sq_nonneg b)]

/-- Sum of cubes bounded by cube of the sum, with no cardinality loss. -/
theorem sum_cube_le_cube_sum {I : Type*} (s : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : ∑ i ∈ s, f i ^ 3 ≤ (∑ i ∈ s, f i) ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsmall := ih hfs
    have hcube := cube_add_ge hfi (Finset.sum_nonneg hfs)
    linarith

/-- The reciprocal-factor barrier is a cubic supersolution when its heat
operator is bounded below by the sum of the factor cubes. -/
theorem cubic_barrier_supersolution {q S H G : ℝ}
    (hq : 0 ≤ q) (hS : 0 ≤ S) (hH : 0 ≤ H) (hG : 0 ≤ G) (hHS : H ≤ S ^ 3) :
    q ^ 3 + 4 * H + G ^ 3 ≤ (2 * (q + S) + G) ^ 3 := by
  have h1 := cube_add_ge hq hS
  have h2 := cube_add_ge (by positivity : 0 ≤ 2 * (q + S)) hG
  have hq3 := pow_nonneg hq 3
  have hS3 := pow_nonneg hS 3
  nlinarith

end GlobalPhi43.MW20
