/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffCompactRescale
import Mathlib.Tactic.Linarith

/-!
# Compact affine assembly for the Gamma-difference induction

This module records the compact-set normalization used in the Kolmogorov criterion for models. The
normalized image is a unit parabolic box, while the homeomorphism records the exact inverse relation
required by the Gamma pullback. In the envelope used by the compact rescaling, `B` is random and the
moment bound is a scalar `A`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem gammaDiffCompactSet_normalization
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ (L : ℝ) (hL : 2 ≤ L) (T : Set ParabolicSpace) (f : S ≃ₜ T),
      (∀ z : T, ((f.symm z : S) : ParabolicSpace) =
        (hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm
          (z : ParabolicSpace)) ∧
      (∀ x ∈ T, x.1 ∈ Icc (0 : ℝ) 1 ∧
        ∀ j, x.2 j ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨R, hR0, hR⟩ := hS.isBounded.exists_pos_norm_le
  let L : ℝ := 2 * max 1 R
  have hL : 2 ≤ L := by
    dsimp [L]
    linarith [le_max_left (1 : ℝ) R]
  have hLpos : 0 < L := by linarith
  have hbound (x : ParabolicSpace) (hx : x ∈ S) : ‖x‖ ≤ L / 2 := by
    exact (hR x hx).trans (by
      dsimp [L]
      linarith [le_max_right (1 : ℝ) R])
  let e := hsParabolicBoxHomeomorph hLpos.ne'
  let T : Set ParabolicSpace := e '' S
  let f : S ≃ₜ T := e.image S
  have hf (z : T) : ((f.symm z : S) : ParabolicSpace) =
      (hsParabolicBoxHomeomorph hLpos.ne').symm (z : ParabolicSpace) := by
    rfl
  have hbox : ∀ x ∈ T, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1 := by
    rintro y ⟨x, hx, rfl⟩
    exact hsParabolicBoxHomeomorph_mem_unitBox hL (hbound x hx)
  exact ⟨L, hL, T, f, hf, hbox⟩

end RegularityStructures

end
