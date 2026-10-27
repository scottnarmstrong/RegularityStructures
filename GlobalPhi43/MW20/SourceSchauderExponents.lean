module

public import GlobalPhi43.MW20.OnePointBudgetScale

/-!
# The fixed source exponent family for the radius-local Schauder application
-/

public section

namespace GlobalPhi43.MW20

/-- One source family contains both one-point powers and the three-point power. -/
@[expose] noncomputable def sourceSchauderExponents (ε : ℝ) : Finset ℝ := by
  classical
  exact {1 / 2 - 3 * ε, 1 - 2 * ε, 3 / 2 - 5 * ε}

/-- Every rate lies in the source admissibility interval, with no data dependence. -/
theorem sourceSchauderExponents_admissible {ε : ℝ} (hsmall : ε < 1 / 14) :
    ∀ a ∈ sourceSchauderExponents ε, 0 ≤ a ∧ a ≤ 3 / 2 - 5 * ε := by
  classical
  intro a ha
  simp only [sourceSchauderExponents, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with h | h | h <;> subst a <;> constructor <;> linarith

/-- The three-point alpha rate belongs to the same fixed source family. -/
theorem sourceSchauderExponents_three_point (ε : ℝ) :
    (1 / 2 : ℝ) - 3 * ε ∈ sourceSchauderExponents ε := by
  classical
  simp only [sourceSchauderExponents, Finset.mem_insert, true_or]

/-- Exact finite-family value, including the positive extra alpha term. -/
theorem sourceSchauderExponents_sum {ε T L : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) :
    ∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a) =
      T ^ (1 / 2 - 3 * ε) * L ^ (1 - 2 * ε) +
        T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε) + T ^ (3 / 2 - 5 * ε) := by
  classical
  have hαβ : (1 / 2 : ℝ) - 3 * ε ≠ 1 - 2 * ε := by intro he; linarith
  have hαγ : (1 / 2 : ℝ) - 3 * ε ≠ 3 / 2 - 5 * ε := by intro he; linarith
  have hβγ : (1 : ℝ) - 2 * ε ≠ 3 / 2 - 5 * ε := by intro he; linarith
  have heα : (3 / 2 - 5 * ε) - (1 / 2 - 3 * ε) = 1 - 2 * ε := by ring
  have heβ : (3 / 2 - 5 * ε) - (1 - 2 * ε) = 1 / 2 - 3 * ε := by ring
  unfold sourceSchauderExponents
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, hαβ, hαγ, or_self, not_false_eq_true]),
    Finset.sum_pair hβγ, heα, heβ, sub_self, Real.rpow_zero, mul_one]
  ring

/-- The proved two-exponent one-point bound fits the complete fixed family. -/
theorem sourceSchauderExponents_two_le {ε T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) :
    T ^ (3 / 2 - 5 * ε) + T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε) ≤
      ∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a) := by
  rw [sourceSchauderExponents_sum hε hsmall]
  have hp : 0 ≤ T ^ (1 / 2 - 3 * ε) * L ^ (1 - 2 * ε) := by positivity
  linarith

end GlobalPhi43.MW20
