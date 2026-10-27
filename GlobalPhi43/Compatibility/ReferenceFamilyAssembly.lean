module

public import GlobalPhi43.Compatibility.ReferenceTargets
public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow

/-! Dependent family assembly, preserving specified reference flows and pairwise event order. -/

@[expose] public noncomputable section
namespace GlobalPhi43.Compatibility
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set
open scoped NNReal

/-- Deterministic total profile, selected before any probability space. -/
def totalProfile (K : Target → ℝ → ℝ≥0) (η : NegExponent) : ℝ → ℝ≥0 :=
  if h : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) then K ⟨η,h⟩ else 0

def totalReferenceFlow {Ω : Type*} (ρ : ParabolicSpace → ℝ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (U : (η : Target) → ReferenceAt ρ a ξ hξ η) (η : NegExponent) :
    ℝ → ℝ → HolderBesov η → Ω → HolderBesov η :=
  if h : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) then
    fun t s x ω => (U ⟨η,h⟩).value ω t s x else fun _ _ x _ => x

/-- Assemble a compatible family from the global-flow properties of the specified
reference flows. These properties are hypotheses of the family-choice lemma. -/
theorem exists_total_compatible_family (K : Target → ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (U : (η : Target) → ReferenceAt ρ a ξ (fun ε hε => (hξ ε hε).1) η)
    (hglobal : ∀ η : Target, ∃ μ : Measure (HolderBesov η.1),
      IsGlobalPhi43Flow (K η) P W a η.1
        (Flow.referenceEvent 5 (targetLoss η) ρ a η.1 ξ (fun ε hε => (hξ ε hε).1))
        (fun t s x ω => (U η).value ω t s x) μ) :
    ∃ (Ω₀ : NegExponent → Set Ω)
      (u : (η : NegExponent) → ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
      (μ : (η : NegExponent) → Measure (HolderBesov η)),
      (∀ η : NegExponent, (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) →
        IsGlobalPhi43Flow (totalProfile K η) P W a η (Ω₀ η) (u η) (μ η)) ∧
      ∀ (η γ : NegExponent) (_hη : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)))
        (hηγ : (η:ℝ)<γ) (_hγ : (γ:ℝ) < -(1/2:ℝ)),
        ∀ᵐ ω ∂P, ∀ s t, 0≤s → s≤t → ∀ x : HolderBesov γ,
          holderBesovEmbed η γ hηγ.le (u γ t s x ω) =
            u η t s (holderBesovEmbed η γ hηγ.le x) ω := by
  let E : NegExponent → Set Ω := fun η =>
    if h : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) then
      Flow.referenceEvent 5 (targetLoss ⟨η,h⟩) ρ a η ξ (fun ε hε => (hξ ε hε).1) else ∅
  let μ : (η : NegExponent) → Measure (HolderBesov η) := fun η =>
    if h : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) then (hglobal ⟨η,h⟩).choose else 0
  refine ⟨E,totalReferenceFlow ρ a ξ (fun ε hε => (hξ ε hε).1) U,μ,?_,?_⟩
  · intro η hη
    simpa only [E,μ,totalProfile,totalReferenceFlow,dite_eq_left hη] using (hglobal ⟨η,hη⟩).choose_spec
  · intro η γ hη hηγ hγ
    have hγ' : (γ:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) := ⟨hη.1.trans hηγ,hγ⟩
    simpa only [totalReferenceFlow,dite_eq_left hη,dite_eq_left hγ'] using
      referenceFamily_pair_ae P W hW ρ hρ a ξ hξ U ⟨η,hη⟩ ⟨γ,hγ'⟩ hηγ

/-- The same family assembly with the exact already-total shared deterministic profile.
No additional selection or modification of K is made. -/
theorem exists_compatible_family_shared_profile (K : NegExponent → ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (U : (η : Target) → ReferenceAt ρ a ξ (fun ε hε => (hξ ε hε).1) η)
    (hglobal : ∀ η : Target, ∃ μ : Measure (HolderBesov η.1),
      IsGlobalPhi43Flow (K η.1) P W a η.1
        (Flow.referenceEvent 5 (targetLoss η) ρ a η.1 ξ (fun ε hε => (hξ ε hε).1))
        (fun t s x ω => (U η).value ω t s x) μ) :
    ∃ (Ω₀ : NegExponent → Set Ω)
      (u : (η : NegExponent) → ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
      (μ : (η : NegExponent) → Measure (HolderBesov η)),
      (∀ η : NegExponent, (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) →
        IsGlobalPhi43Flow (K η) P W a η (Ω₀ η) (u η) (μ η)) ∧
      ∀ (η γ : NegExponent) (_hη : (η:ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)))
        (hηγ : (η:ℝ)<γ) (_hγ : (γ:ℝ) < -(1/2:ℝ)),
        ∀ᵐ ω ∂P, ∀ s t, 0≤s → s≤t → ∀ x : HolderBesov γ,
          holderBesovEmbed η γ hηγ.le (u γ t s x ω) =
            u η t s (holderBesovEmbed η γ hηγ.le x) ω := by
  obtain ⟨E,u,μ,hflow,hcomp⟩ := exists_total_compatible_family (fun η => K η.1)
    P W hW ρ hρ a ξ hξ U hglobal
  refine ⟨E,u,μ,?_,hcomp⟩
  intro η hη
  simpa only [totalProfile,dite_eq_left hη] using hflow η hη

end GlobalPhi43.Compatibility
