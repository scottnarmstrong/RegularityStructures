/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.Phi43Size
public import RegularityStructures.Abstract.Model

/-!
# Real constants from the model size

`Model.normOn γ S` is an `ℝ≥0∞`-valued infimum.  A bound `normOn γ S ≤ ofReal B`, `0 ≤ B`, gives
the two real bounds `PiBoundOn γ B S` and `GammaBoundOn γ B S` with the same constant `B`
(`piBoundOn_of_normOn_le`, `gammaBoundOn_of_normOn_le`); monotonicity in the set and in the level
is recorded for `Π` and `Γ`.  The size `phi43Size κ η T Z ψ ≤ ofReal B` then yields the
bounds on the box `phi43Box (T + 1)` at the cutoff `gamma κ`.
-/

public section

open Set
open scoped ENNReal NNReal

namespace RegularityStructures.Phi43.LiftBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : MeasureTheory.Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
  (Z : Model 𝒯 K)

theorem piBoundOn_of_normOn_le {γ B : ℝ} {S : Set E} (hB : 0 ≤ B)
    (h : Z.normOn γ S ≤ ENNReal.ofReal B) : Z.PiBoundOn γ B S := by
  have h1 : Z.piNormOn γ S ≤ ((B.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (le_self_add.trans h).trans (by rw [ENNReal.ofReal])
  have := (Z.piNormOn_le_iff B.toNNReal).1 h1
  rwa [Real.coe_toNNReal _ hB] at this

theorem gammaBoundOn_of_normOn_le {γ B : ℝ} {S : Set E} (hB : 0 ≤ B)
    (h : Z.normOn γ S ≤ ENNReal.ofReal B) : Z.GammaBoundOn γ B S := by
  have h1 : Z.gammaNormOn γ S ≤ ((B.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (le_add_self.trans h).trans (by rw [ENNReal.ofReal])
  have := (Z.gammaNormOn_le_iff B.toNNReal).1 h1
  rwa [Real.coe_toNNReal _ hB] at this

end RegularityStructures.Phi43.LiftBounds

end

public section

namespace RegularityStructures.Phi43.LiftBounds

open scoped ENNReal

variable {κ : Phi43.Kappa} {η T B : ℝ}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
  {ψ : ℝ → C(Torus3, ℝ)}

/-- The `Π`-bound of the size `phi43Size` on the box `phi43Box (T + 1)` at the cutoff `gamma κ`. -/
theorem piBoundOn_of_phi43Size_le (hB : 0 ≤ B)
    (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    Z.PiBoundOn (gamma κ) B (Statements.phi43Box (T + 1)) :=
  piBoundOn_of_normOn_le Z hB (le_self_add.trans h)

/-- The `Γ`-bound of the size `phi43Size` on the box `phi43Box (T + 1)` at the cutoff `gamma κ`. -/
theorem gammaBoundOn_of_phi43Size_le (hB : 0 ≤ B)
    (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    Z.GammaBoundOn (gamma κ) B (Statements.phi43Box (T + 1)) :=
  gammaBoundOn_of_normOn_le Z hB (le_self_add.trans h)

/-- The noise part of the size `phi43Size` is at most `B`. -/
theorem phi43NoiseSize_le_of_phi43Size_le
    (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    Statements.phi43NoiseSize η T ψ ≤ ENNReal.ofReal B :=
  le_add_self.trans h

end RegularityStructures.Phi43.LiftBounds

end
