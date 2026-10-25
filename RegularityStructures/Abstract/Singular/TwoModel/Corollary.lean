/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Theorem71
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum

/-!
# The familiar form of the two-model Theorem 7.1

Choosing `λ = max (max CdPi CdGam) CdGam2 > 0` in `Model.exists_singularDiffBoundOn_kGammaRem`,
all the factors `λ⁻¹ Cd…` are `≤ 1`, and the bound reads
`|||𝒦¹f₁; 𝒦²f₂||| ≤ C K (λ C₁ + Cd)` with `K` built from `max 1 (CΓ₁ ∨ CΓ₂)`, `max CΠ₂ 1`, `CI`,
and the level `γ + 2` analogue, where `λ` is the size of the model difference.
-/

public section

open Set

namespace RegularityStructures

namespace TwoModel

theorem inv_mul_le_one_of_le {lam c : ℝ} (hl : 0 < lam) (hc : c ≤ lam) : lam⁻¹ * c ≤ 1 := by
  rw [inv_mul_le_iff₀ hl]; linarith

theorem max_one_gamConstSum_le {lam a b c : ℝ} (hl : 0 < lam) (hc : c ≤ lam) :
    max 1 (gamConstSum lam a b c) ≤ max 1 (max a b) := by
  unfold gamConstSum
  exact max_le (le_max_left _ _) (max_le (max_le (le_max_right _ _)
    ((inv_mul_le_one_of_le hl hc).trans (le_max_left _ _))) (zero_le_one.trans (le_max_left _ _)))

theorem piConstSum_le {lam CPi CdPi : ℝ} (hl : 0 < lam) (hc : CdPi ≤ lam) :
    piConstSum lam CPi CdPi ≤ max CPi 1 :=
  max_le (le_max_left _ _) ((inv_mul_le_one_of_le hl hc).trans (le_max_right _ _))

end TwoModel

end RegularityStructures

end
