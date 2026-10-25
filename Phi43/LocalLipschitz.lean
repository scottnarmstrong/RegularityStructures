/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.NoiseHyp
public import Phi43.LocalLipschitz.Forcing
public import Phi43.LocalLipschitz.Datum
public import Phi43.LocalLipschitz.Unit
public import Phi43.LocalLipschitz.DuhamelTriangle
public import Phi43.LocalLipschitz.DuhamelNorm
public import Phi43.LocalLipschitz.DuhamelMassive
public import Phi43.LocalLipschitz.DuhamelForcing
public import Phi43.LocalLipschitz.StepConsts
public import Phi43.LocalLipschitz.StepAux
public import Phi43.LocalLipschitz.Step
public import Phi43.LocalLipschitz.OfEnlargedModels

/-!
# The local Lipschitz step for classical solutions

Aggregator: `StoppedContinuity.phi43LocalLipschitz_of_enlargedFamily` (on a short window after any
restart time, the `𝒞^η` distance of two classical solutions grows at most by a fixed factor, up to
the distance of their lifts; conditional on a family of enlarged models) and its ingredients.
-/
