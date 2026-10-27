/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedLocalPDE
public import GlobalPhi43.MW20.SourceExpansionHeat

/-! Exact signed expansion forcing supplied by original bounded-defect
local data, with no global smoothness assumption on the original solution. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

 theorem localData_augmented_expansion_PDE
    {u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ} {C₁ C₂ : ℝ}
    (hd : IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂) :
    ∃ (v : ParabolicSpace → ℝ) (W : Set ParabolicSpace),
      ContDiff ℝ ∞ v ∧ IsOpen W ∧ closure mwCylinder ⊆ W ∧
      EqOn v (fun z => u z - J z) W ∧
      ∀ x z, z ∈ mwCylinder →
        sourceHeat (expansion v Y Z x) z =
          -v z ^ 3 - 3 * v z ^ 2 * J z -
          3 * (v z - v x) * (J z ^ 2 - C₁) - 9 * C₂ * (v z + J z) -
          e₁ z + e₃ z + 3 * v x * e₂ z := by
  obtain ⟨v, W, hv, hW, hKW, heq, hpde⟩ := localData_augmented_sourceHeat hd
  refine ⟨v, W, hv, hW, hKW, heq, ?_⟩
  intro x z hz
  obtain ⟨hvz, hYz, hZz⟩ := hpde z hz
  rw [source_heat_expansion v Y Z hv hd.2.2.2.1 hd.2.2.2.2.1 x z, hvz, hYz, hZz]
  ring

end GlobalPhi43.Local
