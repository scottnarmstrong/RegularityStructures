module

public import GlobalPhi43.Markov.VectorLaw
public import GlobalPhi43.Markov.ObservationClock

/-! # Conditional Markov identities determine all finite observation laws -/

public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GlobalPhi43.Markov

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

/-- Finite-dimensional kernel iteration, including t1=0. All bounded Borel tests
are covered by the asserted measure equality, not just cylinder products. -/
theorem map_observations_eq_observationChain (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ≥0 → Kernel E E) [∀ s, IsMarkovKernel (K s)]
    (U : ℝ≥0 → Ω → E) (m : ℝ≥0 → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hU : ∀ s, Measurable[m s] (U s)) (x : E) (h0 : U 0 =ᵐ[P] fun _ => x)
    (hMarkov : ∀ s t, s ≤ t → ∀ g : E → ℝ,
      Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (U t ω) | m s] =ᵐ[P]
        fun ω => ∫ y, g y ∂K (t - s) (U s ω))
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    P.map (fun ω (i : Fin (n + 1)) => U (t i) ω) = observationChain K t x := by
  have hc := monotone_observationClock t ht
  have he := map_future_eq_finiteChain P (observationSteps K t)
    (fun i => U (observationClock t i)) (fun i => m (observationClock t i))
    (fun i => hm _) (hmono.comp hc) (fun i => hU _) x
    (by simpa only [observationClock] using h0)
    (fun i g hg hb => by
      rw [← observationClock_step K t i]
      exact hMarkov _ _ (hc (Nat.le_succ i)) g hg hb) (n + 1)
  simpa only [observationClock_at, observationChain] using he

end GlobalPhi43.Markov
