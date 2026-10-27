module

public import GlobalPhi43.Markov.FiniteChain

/-! # Observation-time finite chains on the original state carrier -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace GlobalPhi43.Markov

variable {E : Type*} [MeasurableSpace E]

/-- Transition increments for a finite observation tuple. Only indices below m are
used; the zero padding is irrelevant to the m-coordinate chain. -/
def observationSteps (K : ℝ≥0 → Kernel E E) {m : ℕ} (t : Fin m → ℝ≥0)
    (i : ℕ) : Kernel E E :=
  if hi : i < m then
    if h0 : i = 0 then K (t ⟨i, hi⟩)
    else K (t ⟨i, hi⟩ - t ⟨i - 1, by omega⟩)
  else K 0

instance observationSteps_isMarkov (K : ℝ≥0 → Kernel E E)
    [∀ s, IsMarkovKernel (K s)] {m : ℕ} (t : Fin m → ℝ≥0) (i : ℕ) :
    IsMarkovKernel (observationSteps K t i) := by
  unfold observationSteps
  split_ifs <;> infer_instance

/-- The actual kernel E → E^m at the supplied finite nonnegative times.
For an increasing tuple, NNReal subtraction is exactly the stated time gap. -/
def observationChain (K : ℝ≥0 → Kernel E E) {m : ℕ} (t : Fin m → ℝ≥0) :
    Kernel E (Fin m → E) := finiteChain (observationSteps K t) m

theorem observationSteps_zero (K : ℝ≥0 → Kernel E E) {m : ℕ}
    (t : Fin (m + 1) → ℝ≥0) : observationSteps K t 0 = K (t 0) := by
  simp [observationSteps]

end GlobalPhi43.Markov
