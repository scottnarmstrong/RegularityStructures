module

public import GlobalPhi43.Flow.GlobalLimitTransfer
public import GlobalPhi43.Flow.EventFlowRestart
public import GlobalPhi43Statements.Defs.IsContinuousMeasurableFlow

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow.EventFlow

/-- Transfer to the same globally defined map after identification. The
reference-flow theorem supplies joint measurability and restart without an
additional measurability or perfection assumption. -/
theorem globalLimit_of_identification {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : ℕ} {κ : Kappa} {η : NegExponent} {E : Set Ω} {A : E → ℕ → LiftData N κ}
    (u : EventFlow E η A)
    (hB1 : GlobalPhi43.IsContinuousMeasurableFlow E (fun t s x ω => u.value ω t s x))
    (s : ℝ) (hs : 0 ≤ s) (x : C(Torus3, ℝ))
    (U : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η)
    (h : IsPhi43Limit P η x U τ v) (hτ : ∀ᵐ ω ∂P, τ ω = ⊤)
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → v ω t = u.value ω (s + t) s (toHolderBesov η x)) :
    IsPhi43Limit P η x U (fun _ => ⊤) (fun ω t => u.value ω (s + t) s (toHolderBesov η x)) := by
  apply GlobalPhi43.Flow.globalLimit_of_ae_identification h ?_ ?_ ?_ hτ heq
  · intro ω
    have hc : Continuous (fun t : ℝ => (s + t, toHolderBesov η x)) := by fun_prop
    exact (u.continuous_on ω s hs).comp hc.continuousOn
      (fun _ ht => ⟨le_add_of_nonneg_right ht, mem_univ _⟩)
  · intro ω
    simpa only [add_zero] using u.initial ω s hs (toHolderBesov η x)
  · intro t ht
    let D := {p : ℝ × ℝ // 0 ≤ p.2 ∧ p.2 ≤ p.1} × HolderBesov η × Ω
    let f : Ω → D := fun ω =>
      (⟨(s + t, s), hs, le_add_of_nonneg_right ht⟩, toHolderBesov η x, ω)
    have hf : Measurable f := by fun_prop
    exact hB1.1.comp hf

end GlobalPhi43.Flow.EventFlow
