module

public import GlobalPhi43.Flow.FunctionalEventFlow
public import GlobalPhi43.Flow.FunctionalShift
public import GlobalPhi43.Flow.SmoothSequenceLaw

/-! Conditional homogeneity of the very same supplied EventFlow, through the
constructed common functional and the actual entire regularisation law. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Producer bindings identify only the actual forcing and fixed drift, not a path limit. -/
theorem eventFlow_common_representation {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent}
    {E : Set Ω} {a : E → ℕ → LiftData N κ} (u : EventFlow E η a)
    (f : Ω → ℕ → SmoothForcing) (b : ℕ → ℝ)
    (hforce : ∀ ω : E, ∀ n, (a ω n).forcing = (f ω.val n).val)
    (hcoeff : ∀ ω : E, liftDriftSequence (a ω) = b)
    (ω : E) (s T : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T) (x : HolderBesov η) :
    sequenceFlowFunctional η b s T x (f ω.val) = u.value ω.val (s + T) s x := by
  have he : liftForcingSequence (a ω) = f ω.val := by
    funext n
    exact Subtype.ext (hforce ω n)
  rw [← he, ← hcoeff ω]
  exact eventFlow_sequenceFunctional_eq u ω s T hs hT x

/-- Conditional finite/countable homogeneity for the same EventFlow. No shifted
producer, ambient noise-generation assumption, or action on Omega is needed for the law. -/
theorem eventFlow_homogeneous_law {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) {ξ : ℕ → Ω → SpaceTime → ℝ}
    (hξ : ∀ n, IsRegularisedNoise P W ρ (ε n) (ξ n))
    {N : ℕ} {κ : Kappa} {η : NegExponent} {E : Set Ω} {a : E → ℕ → LiftData N κ}
    (u : EventFlow E η a) (hE : ∀ᵐ ω ∂P, ω ∈ E) (b : ℕ → ℝ)
    (hforce : ∀ ω : E, ∀ n, (a ω n).forcing = ξ n ω.val)
    (hcoeff : ∀ ω : E, liftDriftSequence (a ω) = b)
    (s : ℝ) (hs : 0 ≤ s) (T : I → ℝ) (hT : ∀ i, 0 ≤ T i) (x : I → HolderBesov η) :
    IdentDistrib (fun ω i => u.value ω (s + T i) s (x i))
      (fun ω i => u.value ω (T i) 0 (x i)) P P := by
  let f := asSmoothSequence ξ (fun n => (hξ n).1)
  have hseq : IdentDistrib (fun ω => shiftSmoothSequence s (f ω)) f P P := by
    exact regularisedSmoothSequence_time_translate_identDistrib hW hρ hε hξ s
  have hcommon := sequenceFunctional_family_identDistrib hseq η b (fun _ : I => 0) T hT x
  have hl : (fun ω i => sequenceFlowFunctional η b 0 (T i) (x i)
      (shiftSmoothSequence s (f ω))) =ᵐ[P] (fun ω i => u.value ω (s + T i) s (x i)) := by
    filter_upwards [hE] with ω hω
    funext i
    rw [← sequenceFlowFunctional_shift]
    exact eventFlow_common_representation u f b hforce hcoeff ⟨ω, hω⟩ s (T i) hs (hT i) (x i)
  have hr : (fun ω i => sequenceFlowFunctional η b 0 (T i) (x i) (f ω)) =ᵐ[P]
      (fun ω i => u.value ω (T i) 0 (x i)) := by
    filter_upwards [hE] with ω hω
    funext i
    simpa only [zero_add] using
      eventFlow_common_representation u f b hforce hcoeff ⟨ω, hω⟩ 0 (T i) le_rfl (hT i) (x i)
  exact ⟨hcommon.aemeasurable_fst.congr hl, hcommon.aemeasurable_snd.congr hr,
    (Measure.map_congr hl).symm.trans (hcommon.map_eq.trans (Measure.map_congr hr))⟩

end GlobalPhi43.Flow
