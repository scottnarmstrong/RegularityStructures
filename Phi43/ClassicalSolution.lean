/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Classical solutions of the regularised equation

A classical solution of `∂_t u = Δu - u³ + c u + f`, `u(0) = u₀`, is continuous on
`[0, ∞) × T³`, smooth on `(0, ∞) × T³`, and satisfies the equation pointwise there. Derivatives are
taken on the spatially periodic lift to `ℝ × ℝ³`. A solution is recorded as a path
`t ↦ u t ∈ C(T³)`; only `t ≥ 0` matters.

Source: the statement, Definition 2.6.
-/

@[expose] public section

open scoped ContDiff

namespace RegularityStructures.Phi43

/-- `u` is a classical solution of `∂_t u = Δu - u³ + c u + f` on `[0, ∞) × T³` with `u(0) = u₀`. -/
structure IsClassicalSolution (c : ℝ) (f : SpaceTime → ℝ) (u₀ : C(Torus3, ℝ))
    (u : ℝ → C(Torus3, ℝ)) : Prop where
  continuousOn : ContinuousOn (fun z : ℝ × Torus3 => u z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  initial : u 0 = u₀
  contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2)) (Set.Ioi 0 ×ˢ Set.univ)
  equation : ∀ t, 0 < t → ∀ y : Fin 3 → ℝ,
    deriv (fun s => u s (torusProj y)) t =
      (∑ i, deriv (deriv fun r => u t (torusProj (Function.update y i r))) (y i))
        - u t (torusProj y) ^ 3 + c * u t (torusProj y) + f (t, torusProj y)

end RegularityStructures.Phi43

end
