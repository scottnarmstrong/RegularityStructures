module

public import GlobalPhi43.Flow.SmoothSolutions
public import GlobalPhi43.Flow.BallCompletion
public import Phi43.BPHZ.GModelsNoiseDist
public import RegularityStructures.BPHZ.ModelNormTriangle

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

@[expose] def smoothRepresentative {η : NegExponent} {R : ℝ} (z : smoothBall η R) : C(Torus3, ℝ) :=
  z.property.choose

theorem smoothRepresentative_spec {η : NegExponent} {R : ℝ} (z : smoothBall η R) :
    IsSmoothOnTorus (smoothRepresentative z) ∧
      toHolderBesov η (smoothRepresentative z) = z.val.val := z.property.choose_spec

@[expose] def curveOnSmooth {η : NegExponent} {R : ℝ} (τ c : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (z : smoothBall η R) : C(Icc (0 : ℝ) τ, HolderBesov η) :=
  smoothCurve η τ c f hf (smoothRepresentative z) (smoothRepresentative_spec z).1

end GlobalPhi43.Flow
