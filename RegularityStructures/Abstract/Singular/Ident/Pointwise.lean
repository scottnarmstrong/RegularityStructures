/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.FunctionModel
public import RegularityStructures.Abstract.ProductBounds

/-!
# Pointwise comparison of `Π_z f(z)` with the pointwise reconstruction

For a model realised by smooth functions and `f` in the window setting `LayerSettingW`, write
`G_z(y) = fnComb g γ z (f z) y = (Π_z f(z))(y)`.  Then (Remark 3.15 of [Hai14])

* `G_z(y) − R̃f(y) = −∑_j (f(y) − Γ_{yz} f(z))_j g_{y,j}(y)`
  (`abs_fnComb_sub_pointwiseReconstruct_le`), hence, for `d(y, z) ≤ min(w_z, w_y)`, the singular
  increment bound gives `|G_z(y) − R̃f(y)| ≲ d^{γ − deg j} w^{η − γ}` termwise
  (`abs_fnComb_sub_pointwiseReconstruct_le_of_close`);
* a crude uniform bound `|G_z(y)| ≲ (∑_j |g_{y,j}(y)|) w_z^{min(η,0)}` for `z` in the slab and
  `d(y, z) ≤ 8 w_z` (`abs_fnComb_le_of_slab`), which uses the vanishing of `g_{y,j}(y)` for
  `deg j > 0` and the bounds on `Γ_{yz}`.

Source: [Hai14] = arXiv:1303.5113v4, Remark 3.15.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The constant `∑_{j, i} 8^{deg i − deg j}` of the crude bound. -/
noncomputable def identDomConst (𝒯 : RegularityStructure ι) : ℝ :=
  ∑ j, ∑ i, (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j)

theorem identDomConst_nonneg (𝒯 : RegularityStructure ι) : 0 ≤ identDomConst 𝒯 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _

theorem sum_rpow_eight_le_identDomConst (𝒯 : RegularityStructure ι) (j : ι) :
    ∑ i, (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j) ≤ identDomConst 𝒯 :=
  Finset.single_le_sum (f := fun j => ∑ i, (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _) (Finset.mem_univ j)

end RegularityStructures
