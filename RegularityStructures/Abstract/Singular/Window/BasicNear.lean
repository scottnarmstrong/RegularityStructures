/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.Window.Basic`

The statements of `RegularityStructures.Abstract.Singular.Window.Basic` that involve `Γ`-bounds, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

@[expose] public section

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

end Model

end RegularityStructures

end

public section

open Set

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ CGam : ℝ}

/-- **Γ near base points**: for `x, y` in the window,
`|(Γ_{yx} e_i)_j| ≤ C_Γ d(y, x)^{deg i - deg j}`. -/
theorem abs_gammaMap_single_le_of_window_near (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    {i j : ι} (hi : 𝒯.deg i < γ) (hji : 𝒯.deg j < 𝒯.deg i) {x y : ParabolicSpace}
    (hx : x ∈ hairerTimeWindow) (hy : y ∈ hairerTimeWindow) (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) :
    |M.gammaMap y x (Pi.single i 1) j| ≤ CGam * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j) :=
  hGam i j hi hji x hx y hy hxy

end Model

end RegularityStructures

end
