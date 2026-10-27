module

public import GlobalPhi43.Markov.ObservationChain
public import GlobalPhi43.Invariant.Averages

/-! # Invariant mixtures of finite chains and time-shifted observation laws -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace GlobalPhi43.Invariant

open GlobalPhi43.Markov

variable {E : Type*} [MeasurableSpace E]

/-- Integrating the finite chain against its initial law propagates only the first
kernel; all remaining kernels and the whole vector test stay fixed. -/
theorem integral_mixed_finiteChain_succ (κ : ℕ → Kernel E E)
    [∀ i, IsMarkovKernel (κ i)] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) {F : (Fin (n + 1) → E) → ℝ} (hF : Measurable F)
    (C : ℝ) (hC : ∀ v, ‖F v‖ ≤ C) :
    (∫ v, F v ∂(finiteChain κ (n + 1) ∘ₘ μ)) =
      ∫ y, ∫ v, F (Fin.cons y v) ∂finiteChain (fun i => κ (i + 1)) n y ∂(κ 0 ∘ₘ μ) := by
  let H : E → ℝ := fun y => ∫ v, F (Fin.cons y v)
    ∂finiteChain (fun i => κ (i + 1)) n y
  have hm : Measurable H :=
    (hF.comp (measurable_finCons n)).stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hb (y : E) : ‖H y‖ ≤ C := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := finiteChain (fun i => κ (i + 1)) n y)
        (ae_of_all _ fun v => hC (Fin.cons y v))
  rw [integral_bind_bounded μ (finiteChain κ (n + 1)) hF C hC]
  simp_rw [integral_finiteChain_succ κ n _ hF C hC]
  exact (integral_bind_bounded μ (κ 0) hm C hb).symm

/-- Equal propagated initial laws and identical later transitions give the same
entire vector law. This is a measure equality, so it covers arbitrary Borel tests. -/
theorem mixed_finiteChain_eq (κ κ' : ℕ → Kernel E E)
    [∀ i, IsMarkovKernel (κ i)] [∀ i, IsMarkovKernel (κ' i)]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (htail : ∀ i, κ (i + 1) = κ' (i + 1))
    (hfirst : κ 0 ∘ₘ μ = κ' 0 ∘ₘ ν) (n : ℕ) :
    finiteChain κ (n + 1) ∘ₘ μ = finiteChain κ' (n + 1) ∘ₘ ν := by
  apply Markov.measure_eq_of_bounded_integrals
  intro F hF hB
  obtain ⟨C, hC⟩ := hB
  have hb (v) : ‖F v‖ ≤ C := by simpa only [Real.norm_eq_abs] using hC v
  rw [integral_mixed_finiteChain_succ κ μ n hF C hb,
    integral_mixed_finiteChain_succ κ' ν n hF C hb, hfirst]
  have he : (fun i => κ (i + 1)) = fun i => κ' (i + 1) := funext htail
  rw [he]

/-- A simultaneous nonnegative shift leaves every later time gap unchanged. -/
theorem observationSteps_shift_tail (K : ℝ≥0 → Kernel E E) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (r : ℝ≥0) (i : ℕ) :
    observationSteps K (fun j => r + t j) (i + 1) = observationSteps K t (i + 1) := by
  by_cases hi : i + 1 < n + 1
  · simp [observationSteps, hi, add_tsub_add_eq_tsub_left]
  · simp [observationSteps, hi]

/-- One fixed invariant probability gives all nonnegative shifted finite-chain laws.
No new invariant measure or subsequence is selected for the time tuple or shift. -/
theorem observationChain_comp_shift_eq (K : ℝ≥0 → Kernel E E)
    [∀ s, IsMarkovKernel (K s)] (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : ∀ s, K s ∘ₘ μ = μ) {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (r : ℝ≥0) :
    observationChain K (fun j => r + t j) ∘ₘ μ = observationChain K t ∘ₘ μ := by
  apply mixed_finiteChain_eq (observationSteps K (fun j => r + t j)) (observationSteps K t)
    μ μ (fun i => observationSteps_shift_tail K t r i)
  rw [observationSteps_zero, observationSteps_zero, hμ, hμ]

end GlobalPhi43.Invariant
