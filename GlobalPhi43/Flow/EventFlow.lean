module

public import GlobalPhi43.Flow.AllHorizonProperties

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Uses the one pre-existing event and its actual family. No event is selected
by this construction, and no measurability/perfection assertion is implicit. -/
structure EventFlow {Ω : Type*} {N : ℕ} {κ : Kappa} (E : Set Ω) (η : NegExponent)
    (a : E → ℕ → LiftData N κ) where
  system : ∀ ω : E, FiniteLimitSystem η (a ω)

/-- Deterministic flow construction from the two explicit analytic inputs. -/
theorem exists_eventFlow {Ω : Type*} {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (E : Set Ω) (a : E → ℕ → LiftData N κ)
    (inputs : ∀ ω : E, FiniteAnalyticInputs η (a ω)) : Nonempty (EventFlow E η a) := by
  exact ⟨⟨fun ω => Classical.choice (exists_finiteLimitSystem hκE hN hη hκη (inputs ω))⟩⟩

namespace EventFlow

variable {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent} {E : Set Ω}
  {a : E → ℕ → LiftData N κ}

/-- The single absolute-time map, exactly equal to the datum off E. -/
@[expose] def value (u : EventFlow E η a) (ω : Ω) (t s : ℝ) (x : HolderBesov η) : HolderBesov η := by
  classical
  exact if h : ω ∈ E then (u.system ⟨ω, h⟩).evolution t s x else x

theorem value_on (u : EventFlow E η a) (ω : E) (t s : ℝ) (x : HolderBesov η) :
    u.value ω.val t s x = (u.system ω).evolution t s x := by
  simp only [value, dite_eq_left ω.property]

theorem value_off (u : EventFlow E η a) {ω : Ω} (hω : ω ∉ E) (t s : ℝ) (x : HolderBesov η) :
    u.value ω t s x = x := by simp only [value, dite_eq_right hω]

theorem initial (u : EventFlow E η a) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) (x : HolderBesov η) :
    u.value ω s s x = x := by
  by_cases hω : ω ∈ E
  · rw [u.value_on ⟨ω, hω⟩, FiniteLimitSystem.evolution, sub_self]
    exact (u.system ⟨ω, hω⟩).initial s hs x
  · exact u.value_off hω s s x

/-- Joint time/data continuity at every fixed nonnegative start, for every
omega, using a larger finite chart at data/time boundaries. -/
theorem continuous_on (u : EventFlow E η a) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × HolderBesov η => u.value ω p.1 s p.2) (Ici s ×ˢ univ) := by
  by_cases hω : ω ∈ E
  · have he := (u.system ⟨ω, hω⟩).continuous_on s hs
    have hc : Continuous (fun p : ℝ × HolderBesov η => (p.1 - s, p.2)) := by fun_prop
    have hm : MapsTo (fun p : ℝ × HolderBesov η => (p.1 - s, p.2))
        (Ici s ×ˢ univ) (Ici (0 : ℝ) ×ˢ univ) := by
      intro p hp
      exact ⟨sub_nonneg.mpr hp.1, mem_univ _⟩
    simpa only [value, dite_eq_left hω, FiniteLimitSystem.evolution, Function.comp_def] using
      he.comp hc.continuousOn hm
  · simpa only [value, dite_eq_right hω] using
      (continuous_snd.continuousOn : ContinuousOn (fun p : ℝ × HolderBesov η => p.2) (Ici s ×ˢ univ))

end EventFlow
end GlobalPhi43.Flow
