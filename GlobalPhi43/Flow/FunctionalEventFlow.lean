module

public import GlobalPhi43.Flow.SequenceFunctional
public import GlobalPhi43.Flow.EventFlow

/-! Identification of the common functional with the existing producer's map.
This module consumes the charts and flow; it constructs neither a flow nor an event. -/

public noncomputable section

open MeasureTheory Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The actual full smooth-forcing sequence underlying a supplied lift family. -/
@[expose] def liftForcingSequence {N : ℕ} {κ : Kappa} (a : ℕ → LiftData N κ) :
    ℕ → SmoothForcing := fun n => ⟨(a n).forcing, smooth_of_moderateLift (a n).moderate⟩

@[expose] def liftDriftSequence {N : ℕ} {κ : Kappa} (a : ℕ → LiftData N κ) : ℕ → ℝ :=
  fun n => 3 * (a n).constants.1 - 9 * (a n).constants.2

/-- At a fixed smooth datum the existing chart limits are the actual classical endpoints. -/
theorem finiteSystem_classical_tendsto {N : ℕ} {κ : Kappa} {η : NegExponent}
    {a : ℕ → LiftData N κ} (sys : FiniteLimitSystem η a)
    (s T : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    Tendsto (fun n => sequenceClassicalEndpoint η (liftDriftSequence a) n s T q hq
      (liftForcingSequence a)) atTop (𝓝 (sys.value s T (toHolderBesov η q))) := by
  let j := FiniteLimitSystem.level s T (toHolderBesov η q)
  have hb := FiniteLimitSystem.level_bounds s T (toHolderBesov η q)
  let c := sys.chart j
  let st : Icc (0 : ℝ) (j + 1) := ⟨s, hs, hb.1⟩
  let z : StateBall η (j + 1) := ⟨toHolderBesov η q, by
    simpa only [mem_closedBall, dist_zero_right] using hb.2.2⟩
  let zq : smoothBall η (j + 1) := ⟨z, q, hq, rfl⟩
  let r : Icc (0 : ℝ) (j + 1) := ⟨T, hT, hb.2.1⟩
  obtain ⟨he, ht⟩ := sys.smooth_approx_on_chart c st z (fun _ => zq) tendsto_const_nhds
  have hv := ((continuous_eval_const r).tendsto (c.limit (st, z))).comp ht
  rw [he r] at hv
  convert hv using 1
  funext n
  dsimp only [Function.comp_def]
  rw [curveOnSmooth_eq _ _ _ _ zq q hq rfl]
  rfl

/-- Pointwise identification on every supplied finite-limit system, including rough data. -/
theorem finiteSystem_sequenceFunctional_eq {N : ℕ} {κ : Kappa} {η : NegExponent}
    {a : ℕ → LiftData N κ} (sys : FiniteLimitSystem η a)
    (s T : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T) (x : HolderBesov η) :
    sequenceFlowFunctional η (liftDriftSequence a) s T x (liftForcingSequence a) =
      sys.value s T x := by
  have hi (j : ℕ) : sequenceSmoothLimit η (liftDriftSequence a) s T j x (liftForcingSequence a) =
      sys.value s T (toHolderBesov η (smoothApprox η j x)) :=
    limitOr_eq_of_tendsto x (finiteSystem_classical_tendsto sys s T hs hT _ (smoothApprox_smooth η j x))
  apply limitOr_eq_of_tendsto
  simp_rw [hi]
  have hp : Tendsto (fun j => (T, toHolderBesov η (smoothApprox η j x))) atTop (𝓝 (T, x)) :=
    tendsto_const_nhds.prodMk_nhds (smoothApprox_tendsto η x)
  have hd : ∀ᶠ j in atTop,
      (T, toHolderBesov η (smoothApprox η j x)) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (HolderBesov η)) :=
    Eventually.of_forall fun _ => ⟨hT, mem_univ _⟩
  exact (sys.continuous_on s hs (T, x) ⟨hT, mem_univ _⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hp, hd⟩)

/-- Same EventFlow, same event, same actual forcing family; no new flow or exceptional set. -/
theorem eventFlow_sequenceFunctional_eq {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent}
    {E : Set Ω} {a : E → ℕ → LiftData N κ} (u : EventFlow E η a)
    (ω : E) (s T : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T) (x : HolderBesov η) :
    sequenceFlowFunctional η (liftDriftSequence (a ω)) s T x (liftForcingSequence (a ω)) =
      u.value ω.val (s + T) s x := by
  rw [u.value_on ω, FiniteLimitSystem.evolution, add_sub_cancel_left]
  exact finiteSystem_sequenceFunctional_eq (u.system ω) s T hs hT x

end GlobalPhi43.Flow
