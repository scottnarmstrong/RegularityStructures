/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Translate.Model
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# Restart by time translation: window and slab bounds of a translate

For the restart time `s`, the translate `Z.translate (s, 0)` has `Π`- and `Γ`-bounds on Hairer's
window `[-1, 2] × ℝ³` (resp. on the slab `(0, 1] × ℝ³`) exactly when `Z` has the same bounds on the
time strip `[s - 1, s + 2] × ℝ³` (resp. `(s, s + 1] × ℝ³`).  These are specialisations of
`Model.piBoundOn_translate_iff` and `Model.gammaBoundOn_translate_iff`.
-/

@[expose] public section

open Set

namespace RegularityStructures.Phi43.LiftBounds

/-- The restart translation `(s, 0)`. -/
def restartPoint (s : ℝ) : ParabolicSpace := (s, 0)

/-- The time strip `[a, b] × ℝ³`. -/
def timeStrip (a b : ℝ) : Set ParabolicSpace := {z | a ≤ z.1 ∧ z.1 ≤ b}

end RegularityStructures.Phi43.LiftBounds

end

public section

open Set

namespace RegularityStructures.Phi43.LiftBounds

theorem image_add_restartPoint_timeStrip (s a b : ℝ) :
    (· + restartPoint s) '' timeStrip a b = timeStrip (a + s) (b + s) := by
  ext z
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simp [restartPoint]; linarith, by simp [restartPoint]; linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨z - restartPoint s, ⟨?_, ?_⟩, by simp⟩
    · simp [restartPoint]; linarith
    · simp [restartPoint]; linarith

theorem hairerTimeWindow_eq_timeStrip : hairerTimeWindow = timeStrip (-1) 2 := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (Z : Model 𝒯 parabolicSemigroup) (s : ℝ) {γ C : ℝ}

/-- `Π`-bound of the restarted model on the window, from the strip bound. -/
theorem piBoundOn_translate_window :
    (Z.translate (restartPoint s)).PiBoundOn γ C hairerTimeWindow ↔
      Z.PiBoundOn γ C (timeStrip (-1 + s) (2 + s)) := by
  rw [Model.piBoundOn_translate_iff, hairerTimeWindow_eq_timeStrip,
    image_add_restartPoint_timeStrip]

end RegularityStructures.Phi43.LiftBounds

end
