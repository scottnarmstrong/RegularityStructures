module

public import GlobalPhi43.Flow.SequenceFunctional
public import GlobalPhi43.Flow.ClassicalTranslation

/-! Exact shift identities of the common functional, before any noise space. -/

public noncomputable section

open RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

@[expose] def shiftSmoothSequence (s : ℝ) (f : ℕ → SmoothForcing) : ℕ → SmoothForcing :=
  fun n => ⟨shiftForcing s (f n).val, isSmoothOnSpaceTime_shiftForcing (f n).property s⟩

theorem sequenceClassicalEndpoint_shift (η : NegExponent) (b : ℕ → ℝ)
    (n : ℕ) (s T : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    (f : ℕ → SmoothForcing) :
    sequenceClassicalEndpoint η b n s T q hq f =
      sequenceClassicalEndpoint η b n 0 T q hq (shiftSmoothSequence s f) := by
  apply congrArg (toHolderBesov η)
  apply smoothSolution_congr_forcing
  funext z
  simp only [shiftSmoothSequence, shiftForcing, add_zero]

theorem sequenceSmoothLimit_shift (η : NegExponent) (b : ℕ → ℝ)
    (s T : ℝ) (j : ℕ) (x : HolderBesov η) (f : ℕ → SmoothForcing) :
    sequenceSmoothLimit η b s T j x f =
      sequenceSmoothLimit η b 0 T j x (shiftSmoothSequence s f) := by
  unfold sequenceSmoothLimit
  congr 1
  funext n
  exact sequenceClassicalEndpoint_shift η b n s T _ _ f

/-- Every external start uses the identical time-zero functional on the shifted sequence. -/
theorem sequenceFlowFunctional_shift (η : NegExponent) (b : ℕ → ℝ)
    (s T : ℝ) (x : HolderBesov η) (f : ℕ → SmoothForcing) :
    sequenceFlowFunctional η b s T x f =
      sequenceFlowFunctional η b 0 T x (shiftSmoothSequence s f) := by
  unfold sequenceFlowFunctional
  congr 1
  funext j
  exact sequenceSmoothLimit_shift η b s T j x f

end GlobalPhi43.Flow
