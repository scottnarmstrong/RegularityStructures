module

public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow
public import GlobalPhi43Statements.Defs.HolderBesovEmbed
import GlobalPhi43.Compatibility.ReferenceFamilyAssembly
import GlobalPhi43.Compatibility.ReferenceFamilyLaws

/-! Compatibility across regularity exponents for a common reference family.
The deterministic shared profile precedes the source probability space;
laws are selected after the specified flows, and compatibility is pairwise almost everywhere. -/

public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures
open scoped NNReal
universe u

theorem exponentCompatibility :
    ∀ (a : ℝ),
    ∃ K : NegExponent → ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W),
    ∃ (Ω₀ : NegExponent → Set Ω)
      (u : (η : NegExponent) → ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
      (μ : (η : NegExponent) → Measure (HolderBesov η)),
      (∀ η : NegExponent, (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)) →
        GlobalPhi43.IsGlobalPhi43Flow (K η) P W a η (Ω₀ η) (u η) (μ η)) ∧
      ∀ (η η'' : NegExponent) (_hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
        (hηη'' : (η : ℝ) < η'') (_hη'' : (η'' : ℝ) < -(1 / 2 : ℝ)),
        ∀ᵐ ω ∂P, ∀ s t, 0 ≤ s → s ≤ t → ∀ x : HolderBesov η'',
          GlobalPhi43.holderBesovEmbed η η'' hηη''.le (u η'' t s x ω) =
            u η t s (GlobalPhi43.holderBesovEmbed η η'' hηη''.le x) ω  := by
  intro a
  refine ⟨Compatibility.compatibilityProfile.{u} a,?_⟩
  intro Ω _ P _ _ W hW
  exact Compatibility.exists_compatible_family_shared_profile
    (Compatibility.compatibilityProfile.{u} a) P W hW
    Attachment.referencePhi0 Attachment.referencePhi0_isMollifier a
    (Attachment.referenceNoiseFamily P W hW)
    (fun _ hε => Attachment.referenceNoiseFamily_spec P W hW hε)
    (Compatibility.commonReferenceFamily a P W hW)
    (fun η => Compatibility.commonReferenceFamily_global.{u} a η P W hW)

end GlobalPhi43
