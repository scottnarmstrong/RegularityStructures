/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.Compactness.Compact

/-!
# Compact sublevels of a stronger norm

Compactness follows from the stronger-sublevel theorem.
-/

public section

namespace GlobalPhi43

open Set RegularityStructures
open scoped ENNReal NNReal

/-- Sublevel sets of the stronger norm are compact in the weaker topology. -/
theorem compactSublevel :
    ∀ (η β η'' : NegExponent) (hηβ : (η : ℝ) ≤ β) (_hβ : (β : ℝ) < η'') (M : ℝ≥0),
      IsCompact {z : HolderBesov η | extNorm η η'' z ≤ M} ∧
      ∀ z : HolderBesov η, extNorm η η'' z ≤ M →
        ∃ w : HolderBesov β, holderBesovEmbed η β hηβ w = z ∧ ((η : ℝ) < β → ‖w‖ₑ ≤ (M : ℝ≥0∞)) := by
  intro η β η'' hηβ hβ M
  obtain ⟨hc, he, _⟩ := compact_strongerNorm_sublevel η β η'' hηβ hβ
    (M := (M : ℝ≥0∞)) ENNReal.coe_ne_top
  refine ⟨hc, fun z hz => ?_⟩
  obtain ⟨w, hw, hnorm⟩ := he z hz
  exact ⟨w, hw, fun _ => hnorm⟩

end GlobalPhi43
