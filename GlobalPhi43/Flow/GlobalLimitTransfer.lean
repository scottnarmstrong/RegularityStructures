module

public import GlobalPhi43.Flow.GlobalLifetime

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- Transfer A1--A3 to the constructed global path after the lifetime and path
identification have been proved. Global continuity/initial values hold at
every outcome, so no redefinition on a new exceptional event is necessary. -/
theorem globalLimit_of_ae_identification {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {η : NegExponent} {x : C(Torus3, ℝ)} {U : ℝ → Ω → ℝ → C(Torus3, ℝ)}
    {τ : Ω → ℝ≥0∞} {v g : Ω → ℝ → HolderBesov η}
    (h : IsPhi43Limit P η x U τ v)
    (hg : ∀ ω, ContinuousOn (g ω) (Ici (0 : ℝ)))
    (hg0 : ∀ ω, g ω 0 = toHolderBesov η x)
    (hgm : ∀ t, 0 ≤ t → Measurable (fun ω => g ω t))
    (hτ : ∀ᵐ ω ∂P, τ ω = ⊤)
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → v ω t = g ω t) :
    IsPhi43Limit P η x U (fun _ => ⊤) g := by
  refine ⟨measurable_const, fun _ => by simp, ?_, hg0, ?_, ?_, ?_⟩
  · intro ω
    have he : {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < (⊤ : ℝ≥0∞)} = Ici (0 : ℝ) := by
      ext t
      simp
    rw [he]
    exact hg ω
  · intro t ht B hB
    have he : {ω | ENNReal.ofReal t < (⊤ : ℝ≥0∞) ∧ g ω t ∈ B} = (fun ω => g ω t) ⁻¹' B := by
      ext ω
      simp
    rw [he]
    exact (hgm t ht) hB
  · intro _ hlt
    exact ((lt_irrefl (⊤ : ℝ≥0∞)) hlt).elim
  · intro T hT δ hδ
    have he (ε : ℝ) :
        P {ω | ENNReal.ofReal T < (⊤ : ℝ≥0∞) ∧
          ∃ t ∈ Icc (0 : ℝ) T, δ < ‖toHolderBesov η (U ε ω t) - g ω t‖} =
        P {ω | ENNReal.ofReal T < τ ω ∧
          ∃ t ∈ Icc (0 : ℝ) T, δ < ‖toHolderBesov η (U ε ω t) - v ω t‖} := by
      apply measure_congr
      filter_upwards [hτ, heq] with ω hτω hω
      simp only [hτω, ENNReal.ofReal_lt_top, true_and]
      apply propext
      apply exists_congr
      intro t
      exact and_congr_right (fun ht => by rw [hω t ht.1])
    have hf := funext he
    change Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 0)
    rw [hf]
    exact h.converges T hT δ hδ

end GlobalPhi43.Flow
