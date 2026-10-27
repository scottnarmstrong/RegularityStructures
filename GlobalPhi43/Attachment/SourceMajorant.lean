module

public import GlobalPhi43.Attachment.RegularisedMajorant
public import GlobalPhi43.Flow.WindowEvent

/-! # The literal N=5 source observable at every regularisation scale -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment

open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ENNReal NNReal

/-- Exactly M_epsilon on (0,1]. Only inadmissible scales use zero; there is
NO outcome or growth-event fallback. The reference loss fixes eta_kappa. -/
def sourceMajorant {Ω : Type*} (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (ρ : ParabolicSpace → ℝ) (mass : ℝ) (c : ℝ≥0) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hs : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω)) (ε : ℝ) (ω : Ω) : ℝ := by
  classical
  exact if he : ε ∈ Ioc (0 : ℝ) 1 then
    regularisedMajorant 5 κ Φ hΦ (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0)
      (Flow.coverRegion 0) (Flow.lossExponent κ) c (ξ ε) (hs ε he) ω else 0

theorem sourceMajorant_of_mem {Ω : Type*} (κ : Kappa) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (ρ : ParabolicSpace → ℝ) (mass : ℝ) (c : ℝ≥0)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hs : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ε : ℝ) (he : ε ∈ Ioc (0 : ℝ) 1) :
    sourceMajorant κ Φ hΦ ρ mass c ξ hs ε =
      regularisedMajorant 5 κ Φ hΦ (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0)
        (Flow.coverRegion 0) (Flow.lossExponent κ) c (ξ ε) (hs ε he) := by
  funext ω
  simp only [sourceMajorant, dite_eq_left he]

/-- Everywhere measurability/nonnegativity of the actual source M_epsilon. -/
theorem sourceMajorant_measurable_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ParabolicSpace → ℝ}
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (mass : ℝ) (c : ℝ≥0) (ε : ℝ) :
    Measurable (sourceMajorant κ Φ hΦ ρ mass c ξ (fun e he => (hξ e he).1) ε) ∧
      ∀ ω, 0 ≤ sourceMajorant κ Φ hΦ ρ mass c ξ (fun e he => (hξ e he).1) ε ω := by
  classical
  by_cases he : ε ∈ Ioc (0 : ℝ) 1
  · rw [sourceMajorant_of_mem κ Φ hΦ ρ mass c ξ _ ε he]
    exact regularisedMajorant_measurable_nonneg (hξ ε he) 5 κ Φ hΦ
        (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0)
        (Flow.coverRegion 0) (isCompact_coverRegion 0) (Flow.lossExponent κ) c
  · have hz : sourceMajorant κ Φ hΦ ρ mass c ξ (fun e he => (hξ e he).1) ε = fun _ => 0 := by
      funext ω
      simp only [sourceMajorant, dite_eq_right he]
    rw [hz]
    exact ⟨measurable_const, fun _ => le_rfl⟩

/-- The real source observable equals the full finite ENNReal expression
at EVERY outcome, including the complement of G_epsilon. -/
theorem ofReal_sourceMajorant {Ω : Type*} (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (ρ : ParabolicSpace → ℝ)
    (mass : ℝ) (c : ℝ≥0) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hs : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ε : ℝ) (he : ε ∈ Ioc (0 : ℝ) 1) (ω : Ω) :
    ENNReal.ofReal (sourceMajorant κ Φ hΦ ρ mass c ξ hs ε ω) =
      ENNReal.ofReal (2*c) * max 2 (attachmentFunctional 5 κ Φ hΦ (ξ ε ω)
        (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0) (Flow.coverRegion 0)) +
      noiseSlice 5 (Flow.lossExponent κ) 0 (ξ ε) (hs ε he) ω := by
  simpa only [sourceMajorant, dite_eq_left he] using
    ofReal_regularisedMajorant 5 κ Φ hΦ (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0)
      (Flow.coverRegion 0) (isCompact_coverRegion 0) (Flow.lossExponent κ) c (ξ ε) (hs ε he) ω

end GlobalPhi43.Attachment
