module

public import GlobalPhi43.Attachment.TreeFunctionalLaw
public import GlobalPhi43.Attachment.MajorantRegions

/-! # Everywhere real majorant and its space-independent observable law -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment

open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped NNReal ENNReal

/-- One fixed map of the two literal source observables. Finiteness below
ensures that toReal changes no value, even off the noise-growth event. -/
def majorantCombine (c : ℝ≥0) (v : ℝ≥0∞ × ℝ≥0∞) : ℝ :=
  2 * c * max 2 v.1.toReal + v.2.toReal

theorem measurable_majorantCombine (c : ℝ≥0) : Measurable (majorantCombine c) := by
  exact (measurable_const.mul (measurable_const.max
    (ENNReal.measurable_toReal.comp measurable_fst))).add
      (ENNReal.measurable_toReal.comp measurable_snd)

theorem majorantCombine_nonneg (c : ℝ≥0) (v : ℝ≥0∞ × ℝ≥0∞) : 0 ≤ majorantCombine c v := by
  unfold majorantCombine
  positivity

/-- The actual source expression at every outcome; no event indicator is used. -/
def regularisedMajorant {Ω : Type*} (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (η : NegExponent) (c : ℝ≥0)
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) : ℝ :=
  majorantCombine c (attachmentFunctional N κ Φ hΦ (ξ ω) C S, noiseSlice N η 0 ξ hs ω)

/-- Ambient measurability and nonnegativity are everywhere, not merely on G_epsilon. -/
theorem regularisedMajorant_measurable_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ParabolicSpace → ℝ}
    {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) (hS : IsCompact S)
    (η : NegExponent) (c : ℝ≥0) :
    Measurable (regularisedMajorant N κ Φ hΦ C S η c ξ hξ.1) ∧
      ∀ ω, 0 ≤ regularisedMajorant N κ Φ hΦ C S η c ξ hξ.1 ω := by
  obtain ⟨hF, hJ⟩ := regularised_attachment_measurable hξ N κ Φ hΦ C S hS η 0
  exact ⟨(measurable_majorantCombine c).comp (hF.1.prodMk hJ.1),
    fun ω => majorantCombine_nonneg c _⟩

/-- The real majorant represents exactly the finite extended source expression. -/
theorem ofReal_regularisedMajorant {Ω : Type*} (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (hS : IsCompact S) (η : NegExponent) (c : ℝ≥0)
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) :
    ENNReal.ofReal (regularisedMajorant N κ Φ hΦ C S η c ξ hs ω) =
      ENNReal.ofReal (2 * c) * max 2 (attachmentFunctional N κ Φ hΦ (ξ ω) C S) +
        noiseSlice N η 0 ξ hs ω := by
  have hF := attachmentFunctional_ne_top N κ Φ hΦ (hs ω) C S hS
  have hJ : noiseSlice N η 0 ξ hs ω ≠ ⊤ :=
    (smoothNoiseSlice_lt_top N η 0 (asSmoothNoise ξ hs ω)).ne
  dsimp only [regularisedMajorant, majorantCombine]
  rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_max,
    ENNReal.ofReal_toReal hF, ENNReal.ofReal_toReal hJ]
  norm_num

end GlobalPhi43.Attachment
