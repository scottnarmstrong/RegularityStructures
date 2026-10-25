/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Control of the extended model on the time slab by the window norm of `M`

Window versions of the `Γ` bounds for the extended model: Hairer's extension estimates (5.18)
[Hai14, Theorem 5.14] applied to the extended model `M' = H.intExtend hmeas` of `IntExtHyp`. At a
level `0 < γ' ≤ γ` with `γ' ≤ deg d + 2` for `d ∈ D`, the window bounds of `M'` at level `γ'` are
those of `M` (`RegularityStructures.Abstract.IntExt.Bounds`), and if the symbols of `𝒯'` of degree
in `[γ', γ' + 2)` are integrals of `V'`-symbols of degree `< γ'` (`hmap`):

* `exists_gammaBoundOn_intExtend_win`:
  `M'.GammaBoundOn (γ' + 2) (max C_Γ (c (C_I' + C_Π max(C_Γ, 1)) max(C_Γ, 1))) (timeSlab 1)`;
* `exists_gammaDiffBoundOn_intExtend_win`: the difference version for two extensions of two models
  with the same `IntegrationExtension`:
  `M'₁.GammaDiffBoundOn M'₂ (γ' + 2) (max C_{dΓ} (c (C_{dΠ} G² + C_{dΓ} (C_I' + C_{Π₂} G))))
  (timeSlab 1)`, `G = max (max C_{Γ₁} C_{Γ₂}) 1`.

Here `C_I' = max C_I 1`; `c` is independent of the models.  The qualitative growth model of `M'`
at level `γ'` comes from `H.growth` by `Model.GrowthModel.mono_level` and
`IntExtHyp.growthModel_intExtend`.  The corresponding `Π`-bound at level `γ' + 2` is not a
consequence of window data.
-/

public section

open Set

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ γ' CPi CGam : ℝ} {ρP ρG : ParabolicSpace → ℝ} {p q : ℝ}

/-- A growth model at level `γ` is a growth model at every positive lower level. -/
theorem GrowthModel.mono_level (G : M.GrowthModel γ CPi CGam ρP ρG p q) (hγ' : γ' ≤ γ)
    (hpos : 0 < γ') : M.GrowthModel γ' CPi CGam ρP ρG p q where
  pos := hpos
  moderateP := G.moderateP
  moderateG := G.moderateG
  nonnegG := G.nonnegG
  piBound i hi t ht x := G.piBound i (lt_of_lt_of_le hi hγ') t ht x
  gammaBound i j hi hji x y := G.gammaBound i j (lt_of_lt_of_le hi hγ') hji x y
  piBound_nonneg := G.piBound_nonneg

end Model

end RegularityStructures

end
