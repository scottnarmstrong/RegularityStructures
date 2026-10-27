module

public import GlobalPhi43.Flow.WindowMoments
public import GlobalPhi43.Flow.ReferencePotential
public import GlobalPhi43.Attachment.MajorantRegions
public import GlobalPhi43.Flow.WindowMajorantEnvelope

/-! # All integer model and potential moments, with constants before the noise space -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- The precise compact I=(C_0 union C'_0)+closedBall_p(0,4). -/
theorem isCompact_majorantRegion (s : ℝ) : IsCompact (Flow.majorantRegion s) :=
  ((isCompact_coverRegion s).union (isCompact_sliceRegion s)).add
    (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 4))

/-- Integer-p moments of the model norm. The constant is selected
before the probability space or random family. -/
theorem model_integer_moment (N : ℕ) (hN : 5 ≤ N) (κ : Kappa)
    (hκE : κ.1 ∉ Statements.excludedKappa) (ρ : ParabolicSpace → ℝ)
    (hρ : IsMollifier ρ) (mass : ℝ) (S : Set ParabolicSpace) (hS : IsCompact S)
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ),
        (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) →
      ∀ (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)),
        (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, Statements.IsModeratePhi43Lift N κ (ξ ε ω)
          (wickConstant ρ ε + mass / 3, sunsetConstant ρ ε + 0) (Z ε ω) (ψ ε ω)) →
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (gamma κ) S) P ∧
        ∫⁻ ω, (Z ε ω).normOn (gamma κ) S ^ p ∂P ≤ C := by
  obtain ⟨B, hB, -, -, -⟩ := gModels_constants constantsComparison_limits N hρ hρ (mass / 3, 0)
  obtain ⟨_, C, _, hC, h⟩ := bphzModels_cauchy_shifted
    renormalisedCanonicalModel_existsUnique kolmogorov_modelNorm phi43Noise_cauchy
    (shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds)
    κ hκE N hN ρ ρ hρ hρ S hS p hp (max B 0) (le_max_right _ _)
  refine ⟨NNReal.mk C hC, ?_⟩
  intro Ω _ P _ W hW ξ hξ Z ψ hlift ε hε
  have hz : ∀ e ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, Statements.IsModeratePhi43ModelOf N κ (ξ e ω)
      (shiftConst N ρ e (gModelsShift N ρ (mass / 3, 0) e)) (Z e ω) :=
    fun e he => (hlift e he).mono fun _ hω => isModeratePhi43ModelOf_shiftConst_of_lift hω
  have hb := fun e (he : e ∈ Ioc (0 : ℝ) 1) => (hB e he.1 he.2).trans (le_max_left B 0)
  have hi := h P W hW ξ ξ hξ hξ
    (gModelsShift N ρ (mass / 3, 0)) (gModelsShift N ρ (mass / 3, 0)) hb hb
    Z Z hz hz ε hε ε hε
  exact ⟨hi.1, by simpa only [ENNReal.ofReal_eq_coe_nnreal hC] using hi.2.2.1⟩

/-- Source Y_epsilon on [0,1], bounded by clause (c)'s full [-1,2] window.
The chosen constant precedes the probability space and potential representatives. -/
theorem potential_integer_moment (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ),
        (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) →
      ∀ (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)),
        (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, IsMassivePotential (ξ ε ω) (ψ ε ω)) →
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        ∫⁻ ω, Flow.unitPotentialSize η 0 (ψ ε ω) ^ p ∂P ≤ C := by
  obtain ⟨_, _, h⟩ := (phi43Noise_cauchy.{u} η hη).2.2
  obtain ⟨C, hC, hi⟩ := h ρ ρ hρ hρ 1 le_rfl p hp
  refine ⟨NNReal.mk C hC, ?_⟩
  intro Ω _ P _ W hW ξ hξ ψ hψ ε hε
  have hh := (hi P W hW ξ ξ hξ hξ ψ ψ hψ hψ ε hε ε hε).2.2.1
  rw [← ENNReal.ofReal_eq_coe_nnreal hC]
  apply le_trans (lintegral_mono fun ω => pow_le_pow_left' ?_ p) hh
  apply iSup₂_le
  intro t ht
  exact le_iSup₂_of_le t (show t ∈ Icc (-1 : ℝ) (1 + 1) from
    ⟨by linarith [ht.1], by linarith [ht.2]⟩) le_rfl

end GlobalPhi43.Attachment
