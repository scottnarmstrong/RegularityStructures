/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Persistence.AtZero
public import Phi43.Persistence.Instance
public import Phi43.Persistence.Realising
public import Phi43.Persistence.PotentialOffset
public import Phi43.Persistence.Forcing
public import Phi43.Persistence.NearHyp
public import Phi43.Persistence.Slice
public import Phi43.Persistence.Positive
public import Phi43.Persistence.ClassicalSolution

/-!
# Persistence of classical solutions

Aggregator for `Phi43.Persistence`: the enlarged restarted model `enlargedRestartModel`
(compatibility, growth, joint measurability, kernel realisation at level `κ`), the forcing interface
and the potential bound of the restart from the size of the lift, the `Phi43NearHyp` bundle, the
`𝒞^η` bound of the restarted solution, persistence for start times in `(0, T]`, at start time `0`,
and `phi43_persistence`, which is exactly the persistence clause (i) of
`phi43ClassicalSolution_stoppedContinuity`.
-/
