/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Deterministic
public import Phi43.RegularisedNoise.SmoothVersion.Series
public import Phi43.RegularisedNoise.SmoothVersion.WhiteNoise
public import Phi43.RegularisedNoise.SmoothVersion.Linearity
public import Phi43.RegularisedNoise.SmoothVersion.LinearSums
public import Phi43.RegularisedNoise.SmoothVersion.Growth
public import Phi43.RegularisedNoise.SmoothVersion.PolynomialGrowth
public import Phi43.RegularisedNoise.SmoothVersion.Approximation
public import Phi43.RegularisedNoise.FourierDecayChain
public import Phi43.RegularisedNoise.SmoothModification
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.RegularisedNoise.SmoothVersion.WindowedModes
public import Phi43.RegularisedNoise.SmoothVersion.WindowedKernel
public import Phi43.RegularisedNoise.SmoothVersion.WindowedIntegral
public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientIdentity
public import Phi43.RegularisedNoise.SmoothVersion.TorusSeries
public import Phi43.RegularisedNoise.SmoothVersion.LocalPatching
public import Phi43.RegularisedNoise.SmoothVersion.LatticeSummability
public import Phi43.RegularisedNoise.SmoothVersion.CoordinateFourier
public import Phi43.RegularisedNoise.SmoothVersion.CoordinateDecay
public import Phi43.RegularisedNoise.SmoothVersion.WindowedPatching
public import Phi43.RegularisedNoise.SmoothVersion.TimePeriodise
public import Phi43.RegularisedNoise.SmoothVersion.WindowKernelRegularity
public import Phi43.RegularisedNoise.SmoothVersion.WindowKernelSmoothness
public import Phi43.RegularisedNoise.SmoothVersion.RealTorusSplit
public import Phi43.RegularisedNoise.SmoothVersion.WhiteNoiseLp

/-!
# Smooth version of the regularised noise

This aggregator exports the deterministic support and series criteria together with the white-noise
`L²` and linearity identities, the Borel–Cantelli growth estimate, and the one-step Fourier
integration-by-parts estimate.
-/

@[expose] public section

end
