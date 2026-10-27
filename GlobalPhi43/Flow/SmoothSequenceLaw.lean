module

public import GlobalPhi43.Flow.SequenceFunctional
public import GlobalPhi43.Flow.RegularisedSequenceLaw
public import GlobalPhi43.Attachment.NoiseLawSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Basic.ENNReal.Real

/-! Entire smooth-sequence laws, using the actual versions at every outcome. -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Bundle the full actual sequence, without a growth restriction or fallback. -/
@[expose] def asSmoothSequence {Ω : Type*} (ξ : ℕ → Ω → SpaceTime → ℝ)
    (hξ : ∀ n ω, IsSmoothOnSpaceTime (ξ n ω)) (ω : Ω) : ℕ → SmoothForcing :=
  fun n => ⟨ξ n ω, hξ n ω⟩

theorem asSmoothSequence_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ξ : ℕ → Ω → SpaceTime → ℝ) (hs : ∀ n ω, IsSmoothOnSpaceTime (ξ n ω))
    (hm : ∀ n z, Measurable fun ω => ξ n ω z) : Measurable (asSmoothSequence ξ hs) := by
  apply measurable_pi_iff.mpr
  intro n
  exact Measurable.subtype_mk (measurable_pi_iff.mpr (hm n))

/-- The law of the raw whole sequence determines the law of its actual smooth bundle.
The smooth subset need not be assumed measurable in the ambient raw-function carrier. -/
theorem smoothSequence_identDistrib_of_raw {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    (ξ : ℕ → Ω → SpaceTime → ℝ) (ξ' : ℕ → Ω' → SpaceTime → ℝ)
    (hs : ∀ n ω, IsSmoothOnSpaceTime (ξ n ω))
    (hs' : ∀ n ω, IsSmoothOnSpaceTime (ξ' n ω))
    (hm : ∀ n z, Measurable fun ω => ξ n ω z)
    (hm' : ∀ n z, Measurable fun ω => ξ' n ω z)
    (hLaw : IdentDistrib (fun ω n z => ξ n ω z) (fun ω n z => ξ' n ω z) P P') :
    IdentDistrib (asSmoothSequence ξ hs) (asSmoothSequence ξ' hs') P P' := by
  let e : {f : ℕ → SpaceTime → ℝ // ∀ n, IsSmoothOnSpaceTime (f n)} ≃ᵐ
      (ℕ → SmoothForcing) := MeasurableEquiv.subtypePiEquivPi
  let X := fun ω => e.symm (asSmoothSequence ξ hs ω)
  let Y := fun ω => e.symm (asSmoothSequence ξ' hs' ω)
  have hx : Measurable X := e.symm.measurable.comp (asSmoothSequence_measurable ξ hs hm)
  have hy : Measurable Y := e.symm.measurable.comp (asSmoothSequence_measurable ξ' hs' hm')
  have hsub : IdentDistrib X Y P P' := ⟨hx.aemeasurable, hy.aemeasurable,
    Attachment.subtype_map_eq_of_val_map_eq hLaw.map_eq hx hy⟩
  simpa only [Function.comp_def, X, Y, MeasurableEquiv.apply_symm_apply] using hsub.comp (u := e) e.measurable

/-- Time-translation law of the whole actual smooth bundle. -/
theorem regularisedSmoothSequence_time_translate_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) {ξ : ℕ → Ω → SpaceTime → ℝ}
    (hξ : ∀ n, IsRegularisedNoise P W ρ (ε n) (ξ n)) (s : ℝ) :
    IdentDistrib
      (asSmoothSequence (fun n ω z => ξ n ω (z.1 + s, z.2))
        (fun n ω => isSmoothOnSpaceTime_shiftForcing ((hξ n).1 ω) s))
      (asSmoothSequence ξ (fun n => (hξ n).1)) P P :=
  smoothSequence_identDistrib_of_raw _ _ _ _
    (fun n z => ((hξ n).2 (z.1 + s, z.2)).1) (fun n z => ((hξ n).2 z).1)
    (regularisedSequence_time_translate_identDistrib hW hρ hε hξ s)

/-- Finite or countable observations use the same fixed double-limit functions. -/
theorem sequenceFunctional_family_identDistrib {Ω Ω' I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {X : Ω → ℕ → SmoothForcing} {Y : Ω' → ℕ → SmoothForcing}
    (h : IdentDistrib X Y P P') (η : NegExponent) (b : ℕ → ℝ)
    (s T : I → ℝ) (hT : ∀ i, 0 ≤ T i) (x : I → HolderBesov η) :
    IdentDistrib (fun ω i => sequenceFlowFunctional η b (s i) (T i) (x i) (X ω))
      (fun ω i => sequenceFlowFunctional η b (s i) (T i) (x i) (Y ω)) P P' :=
  h.comp (u := fun f i => sequenceFlowFunctional η b (s i) (T i) (x i) f)
    (measurable_pi_iff.mpr fun i => sequenceFlowFunctional_measurable η b (s i) (T i) (hT i) (x i))

end GlobalPhi43.Flow
