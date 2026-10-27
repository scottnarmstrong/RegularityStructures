module

public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Tactic

public noncomputable section

open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- The additive error coefficient; the first step already costs `K`, not `1`. -/
def restartError (K : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, K ^ (i + 1)

@[simp] theorem restartError_zero (K : ℝ≥0∞) : restartError K 0 = 0 := by
  simp [restartError]

theorem restartError_succ (K : ℝ≥0∞) (n : ℕ) :
    restartError K (n + 1) = K * (restartError K n + 1) := by
  simp [restartError, Finset.sum_range_succ', mul_add, Finset.mul_sum,
    pow_succ']

/-- Exact finite recurrence, retaining the additive model error. -/
theorem finite_restart_recurrence (K D : ℝ≥0∞) (d : ℕ → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ j < N, d (j + 1) ≤ K * (d j + D)) :
    d N ≤ K ^ N * d 0 + restartError K N * D := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun j hj => hstep j (by omega))
    calc
      d (n + 1) ≤ K * (d n + D) := hstep n (by omega)
      _ ≤ K * ((K ^ n * d 0 + restartError K n * D) + D) := by gcongr
      _ = K ^ (n + 1) * d 0 + restartError K (n + 1) * D := by
        simp only [restartError_succ, pow_succ', mul_add, add_mul, mul_one, mul_assoc, add_assoc]

/-- The same bound controls every earlier grid endpoint when `K ≥ 1`. -/
theorem restart_bound_mono {K : ℝ≥0∞} (hK : 1 ≤ K) (a D : ℝ≥0∞) :
    Monotone (fun n : ℕ => K ^ n * a + restartError K n * D) := by
  apply monotone_nat_of_le_succ
  intro n
  apply add_le_add
  · gcongr; omega
  · have hc : restartError K n ≤ restartError K (n + 1) :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ n))
    gcongr

/-- A finite preselected coefficient for the joint initial-data/model error. -/
def finiteRestartFactor (K : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  K ^ n + ∑ i ∈ Finset.range n, K ^ (i + 1)

theorem finiteRestartFactor_bound (K : ℝ≥0) (n : ℕ) (a D : ℝ≥0∞) :
    (K : ℝ≥0∞) ^ n * a + restartError K n * D ≤
      finiteRestartFactor K n * (a + D) := by
  have hc : (finiteRestartFactor K n : ℝ≥0∞) =
      (K : ℝ≥0∞) ^ n + restartError K n := by
    simp [finiteRestartFactor, restartError]
  rw [mul_add, hc]
  exact add_le_add (mul_le_mul' (le_add_right le_rfl) le_rfl)
    (mul_le_mul' (le_add_left le_rfl) le_rfl)

end GlobalPhi43.Flow
