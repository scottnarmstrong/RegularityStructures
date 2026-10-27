module

public import GlobalPhi43.Attachment.SourceMajorant
public import GlobalPhi43.Attachment.AttachmentFunctionalBound
public import GlobalPhi43.Attachment.ConditionalEveryStart
public import GlobalPhi43.Flow.ReferencePotential

/-! # Exact source majorant comparison, conditional only on the named slice row -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- The functional constant is fixed before the noise space.
The time-slice estimate is the sole additional analytic hypothesis,
without a moment or solution bound. -/
theorem sourceMajorant_comparison_of_slice (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (c H : ℝ≥0)
    (hslice : ∀ (a : Flow.LiftData 5 κ) (s : ℝ), 0 ≤ s → ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
        (smoothNoiseJ 5 ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)) ≤
      (H : ℝ≥0∞) * (Flow.unitPotentialSize (Flow.lossExponent κ) s a.potential +
        (1+a.model.normOn (gamma κ) (Flow.majorantRegion s))^3)) :
    ∃ K : ℝ≥0, ∀ {Ω : Type u} (ρ : ParabolicSpace → ℝ) (mass : ℝ)
      (ξ : ℝ → Ω → SpaceTime → ℝ)
      (hs : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
      (ε : ℝ) (_he : ε ∈ Ioc (0 : ℝ) 1) (ω : Ω), ω ∈ growthEvent (ξ ε) →
      ENNReal.ofReal (sourceMajorant κ Φ hΦ ρ mass c ξ hs ε ω) ≤
        (majorantCoefficient c K H : ℝ≥0∞) *
          (1 + (Flow.referenceAttachedModel 5 κ ρ mass ξ hs ε ω).normOn (gamma κ)
            (Flow.majorantRegion 0) + Flow.unitPotentialSize (Flow.lossExponent κ) 0
              (Flow.referencePotential ξ hs ε ω)) ^ 7 := by
  obtain ⟨K, hK, hfunctional⟩ := attachment_functional_bound 5 κ Φ hΦ
  refine ⟨NNReal.mk K hK.le, ?_⟩
  intro Ω ρ mass ξ hs ε he ω hω
  let C : RenormalisationConstants := (wickConstant ρ ε + mass/3, sunsetConstant ρ ε + 0)
  let Z := Flow.referenceAttachedModel 5 κ ρ mass ξ hs ε ω
  let ψ := Flow.referencePotential ξ hs ε ω
  have hZ : Statements.IsModeratePhi43ModelOf 5 κ (ξ ε ω) C Z := by
    dsimp only [Z, Flow.referenceAttachedModel]
    rw [dite_eq_left he]
    exact attachedModel_spec 5 κ (ξ ε) C (hs ε he) ω hω
  let a : Flow.LiftData 5 κ :=
    ⟨ξ ε ω, C, Z, ψ, hω, hZ, Flow.referencePotential_spec ξ hs he hω⟩
  let X := Z.normOn (gamma κ) (Flow.majorantRegion 0)
  let Y := Flow.unitPotentialSize (Flow.lossExponent κ) 0 ψ
  let A := attachmentFunctional 5 κ Φ hΦ (ξ ε ω) C (Flow.coverRegion 0)
  let I4 : Set ParabolicSpace := {y | ∃ z ∈ Flow.coverRegion 0, pdist z y ≤ 4}
  have hfin : Z.normOn (gamma κ) I4 ≠ ⊤ := by
    obtain ⟨_, _, hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement (isCompact_coverRegion 0)
      (by norm_num : (0 : ℝ) ≤ 4))
  have hf := hfunctional (ξ ε ω) C Z (hs ε he ω) hω hZ
    (Flow.coverRegion 0) (isCompact_coverRegion 0)
  have hconvert : ENNReal.ofReal (K * (1 + (Z.normOn (gamma κ) I4).toReal) ^ (7 : ℝ)) =
      (NNReal.mk K hK.le : ℝ≥0∞) * (1 + Z.normOn (gamma κ) I4) ^ 7 := by
    have hpow : (1 + (Z.normOn (gamma κ) I4).toReal) ^ (7 : ℝ) =
        (1 + (Z.normOn (gamma κ) I4).toReal) ^ (7 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (1 + (Z.normOn (gamma κ) I4).toReal) 7
    rw [hpow]
    rw [ENNReal.ofReal_mul hK.le,
      ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hfin, ENNReal.ofReal_eq_coe_nnreal hK.le]
  have hA : A ≤ (NNReal.mk K hK.le : ℝ≥0∞) * (1 + X) ^ 7 := by
    have hn : Z.normOn (gamma κ) I4 ≤ X :=
      attachment_normOn_mono Z (coverRadiusFour_subset_majorant 0)
    exact (hf.trans_eq hconvert).trans (mul_le_mul_right (pow_le_pow_left'
      (add_le_add le_rfl hn) 7) _)
  have hJ : noiseSlice 5 (Flow.lossExponent κ) 0 (ξ ε) (hs ε he) ω ≤
      (H : ℝ≥0∞) * (Y + (1 + X) ^ 3) := by
    rw [noiseSlice_eq]
    refine iSup_le fun t => ?_
    have ht := hslice a 0 le_rfl t.val t.property
    simpa only [a, smoothNoiseJ, zero_add] using ht
  rw [ofReal_sourceMajorant κ Φ hΦ ρ mass c ξ hs ε he ω]
  have hcoef : ENNReal.ofReal (2 * (c : ℝ)) = 2 * (c : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [hcoef]
  exact (add_le_add le_rfl hJ).trans (majorant_rows_le c (NNReal.mk K hK.le) H hA)

end GlobalPhi43.Attachment
