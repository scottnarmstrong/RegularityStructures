module

public import GlobalPhi43.Flow.LimitCocycle

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow.EventFlow

variable {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent} {E : Set Ω}
  {A : E → ℕ → LiftData N κ}

/-- Restart for every rough datum, all real ordered starts, and ALL outcomes.
Outside the same fixed event the identity fallback supplies the assertion. -/
theorem cocycle (u : EventFlow E η A) (ω : Ω) (s r t : ℝ)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (x : HolderBesov η) :
    u.value ω t r (u.value ω r s x) = u.value ω t s x := by
  by_cases hω : ω ∈ E
  · simp only [value, dite_eq_left hω, FiniteLimitSystem.evolution]
    exact (u.system ⟨ω, hω⟩).cocycle s r t hs hsr hrt x
  · simp only [value, dite_eq_right hω]

/-- The restart identity, in its t<=s<=r argument order.
No measurability assertion is inferred from this restart-only interface. -/
theorem b1_restart (u : EventFlow E η A) :
    ∀ t s r, 0 ≤ t → t ≤ s → s ≤ r → ∀ x ω,
      u.value ω r s (u.value ω s t x) = u.value ω r t x := by
  intro t s r ht hts hsr x ω
  exact u.cocycle ω t s r ht hts hsr x

/-- One continuous path on the whole future half-line. No lifetime or chart
choice depends on this start, datum or outcome. -/
@[expose] def globalPath (u : EventFlow E η A) (ω : Ω) (s : ℝ) (hs : 0 ≤ s)
    (x : HolderBesov η) : C(Ici s, HolderBesov η) where
  toFun t := u.value ω t.val s x
  continuous_toFun := (u.continuous_on ω s hs).comp_continuous
    (continuous_subtype_val.prodMk continuous_const) (fun t => ⟨t.property, mem_univ _⟩)

end GlobalPhi43.Flow.EventFlow
