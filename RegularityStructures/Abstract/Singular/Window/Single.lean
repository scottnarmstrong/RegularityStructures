/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Semigroup.Locality.Pairing

/-!
# Window model bound for `Π_z e_i` against scaled test functions

The analogue of `RegularityStructures.Abstract.Singular.ModelPairing.Single` for a model whose
bounds `PiBoundOn γ CPi hairerTimeWindow`, `GammaBoundOn γ CGam hairerTimeWindow` are assumed only
on Hairer's window, together with the *qualitative* growth `Model.HasQualitativeGrowth M γ`. For a
base point `z` such that the closed parabolic ball `{‖· - z‖_𝔰 ≤ 1}` lies in the window (`hball`;
true for `0 ≤ z.1 ≤ 1`, `ball_subset_hairerTimeWindow`) and `φ ∈ B^4`, `0 < λ ≤ 1`:

  `|⟨Π_z e_i, φ^λ_z⟩| ≤ r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π · λ^{deg i}`,

and for `g` scaled at `z` (`IsScaledTest g z R A`)

  `|⟨Π_z e_i, g⟩| ≤ r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π · (A R⁵) R^{deg i}`.

The constant `r4ModelConst 𝒯 γ` depends only on `𝒯` and `γ`; the growth constants enter only
through the existence of the pairing (`RegularisingSemigroup.abs_pairing_le_of_local`).

Source: [Hai14] = arXiv:1303.5113v4, (2.15), Theorem 3.10.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {z : ParabolicSpace} {R A : ℝ}

theorem mem_hairerTimeWindow_of_ball {z : ParabolicSpace}
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow) :
    z ∈ hairerTimeWindow :=
  hball z (by simp [parabolicNorm])

end Model

end RegularityStructures

end
