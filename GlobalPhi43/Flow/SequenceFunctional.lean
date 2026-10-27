module

public import GlobalPhi43.Flow.CommonClassicalEndpoint
public import GlobalPhi43.Flow.SmoothSelectors
public import GlobalPhi43.Flow.MeasurableLimitOr

/-! The prescribed common double-limit functional, total on every smooth sequence. -/

public noncomputable section

open MeasureTheory Filter Topology RegularityStructures

namespace GlobalPhi43.Flow

/-- Inner limit at the selected smooth datum, with fallback equal to the original x. -/
@[expose] def sequenceSmoothLimit (η : NegExponent) (b : ℕ → ℝ) (s T : ℝ)
    (j : ℕ) (x : HolderBesov η) (f : ℕ → SmoothForcing) : HolderBesov η :=
  limitOr x (fun n => sequenceClassicalEndpoint η b n s T
    (smoothApprox η j x) (smoothApprox_smooth η j x) f)

/-- Outer smooth-data limit, again with fallback x. All choices precede noise spaces. -/
@[expose] def sequenceFlowFunctional (η : NegExponent) (b : ℕ → ℝ) (s T : ℝ)
    (x : HolderBesov η) (f : ℕ → SmoothForcing) : HolderBesov η :=
  limitOr x (fun j => sequenceSmoothLimit η b s T j x f)

theorem sequenceSmoothLimit_measurable (η : NegExponent) (b : ℕ → ℝ) (s T : ℝ)
    (hT : 0 ≤ T) (j : ℕ) (x : HolderBesov η) :
    Measurable (sequenceSmoothLimit η b s T j x) :=
  limitOr_measurable (fun _ => x) measurable_const _
    (fun n => sequenceClassicalEndpoint_measurable η b n s T hT _ _)

theorem sequenceFlowFunctional_measurable (η : NegExponent) (b : ℕ → ℝ) (s T : ℝ)
    (hT : 0 ≤ T) (x : HolderBesov η) :
    Measurable (sequenceFlowFunctional η b s T x) :=
  limitOr_measurable (fun _ => x) measurable_const _
    (fun j => sequenceSmoothLimit_measurable η b s T hT j x)

end GlobalPhi43.Flow
