module

public import GlobalPhi43.Markov.ObservationChain

/-! # A finite observation tuple with time zero as its initial observation -/

@[expose] public noncomputable section

open ProbabilityTheory
open scoped NNReal

namespace GlobalPhi43.Markov

/-- Time zero precedes the supplied tuple; padding repeats its last time. -/
def observationClock {n : ℕ} (t : Fin (n + 1) → ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | i + 1 => t ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem observationClock_at {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (i : Fin (n + 1)) :
    observationClock t (i.val + 1) = t i := by
  simp only [observationClock, min_eq_left (Nat.le_of_lt_succ i.isLt)]

theorem monotone_observationClock {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (ht : Monotone t) : Monotone (observationClock t) := by
  apply monotone_nat_of_le_succ
  intro i
  cases i with
  | zero => exact bot_le
  | succ i => exact ht (by change min i n ≤ min (i + 1) n; omega)

/-- Every padded clock increment gives exactly the finite tuple's kernel step. -/
theorem observationClock_step {E : Type*} [MeasurableSpace E]
    (K : ℝ≥0 → Kernel E E) {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (i : ℕ) :
    K (observationClock t (i + 1) - observationClock t i) = observationSteps K t i := by
  cases i with
  | zero => simp [observationClock, observationSteps]
  | succ i =>
    by_cases hi : i + 1 < n + 1
    · simp only [observationClock, min_eq_left (show i + 1 ≤ n by omega),
        min_eq_left (show i ≤ n by omega)]
      simp [observationSteps, hi]
    · simp [observationClock, observationSteps, hi,
        min_eq_right (show n ≤ i + 1 by omega), min_eq_right (show n ≤ i by omega)]

end GlobalPhi43.Markov
