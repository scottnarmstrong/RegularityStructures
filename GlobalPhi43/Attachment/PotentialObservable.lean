module

public import GlobalPhi43.Attachment.NoiseLawSpace
public import Phi43.Stochastic.StochasticHeatConvergencePotentialSmooth
public import Phi43.Stochastic.StochasticHeatConvergenceBesovMeasurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! A common measurable massive-potential window observable. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43

/-- The massive potential of a smooth growing forcing. -/
def noisePotential (f : SmoothGrowingNoise) : ℝ → C(Torus3, ℝ) :=
  (massivePotential_exists_smooth_of_polynomialLift_growth f.1 f.2.1 f.2.2).choose

theorem noisePotential_spec (f : SmoothGrowingNoise) :
    IsMassivePotential f.1 (noisePotential f) ∧
      IsSmoothOnSpaceTime (fun z : SpaceTime => noisePotential f z.1 z.2) ∧
      Continuous (noisePotential f) :=
  (massivePotential_exists_smooth_of_polynomialLift_growth f.1 f.2.1 f.2.2).choose_spec

end GlobalPhi43.Attachment
