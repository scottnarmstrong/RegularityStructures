/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# The space-time window `O_T`

The window `O_T = [-1, T + 1] × [-1, 2]³` in `ℝ × ℝ³`. The cube `[-1, 2]³` contains a fundamental
domain of `T³` with a margin of `1`, so model norms of periodic models on `O_{T+1}` control the
model on `[-1, T + 2] × T³`. The size `phi43Size` and the distance `phi43Dist` of lifts take model
norms on this window, as Hairer's continuity statement takes them on `O = [-1, 2] × ℝ^{d-1}`
[Hai14, Corollary 7.12].

Source: [Hai14, Corollary 7.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The window `O_T = [-1, T+1] × [-1, 2]³`. -/
def Statements.phi43Box (T : ℝ) : Set RegularityStructures.ParabolicSpace :=
  Set.Icc (-1 : ℝ) (T + 1) ×ˢ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 2)

end RegularityStructures.Phi43

end
