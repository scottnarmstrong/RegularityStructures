/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Abstract.QFamilyR4KernelIncrement
public import RegularityStructures.Abstract.QFamilyR4Convolution
public import RegularityStructures.Abstract.Model

/-!
# Mollifying the model at positive time

Ingredients of the converse implication, from Hairer's test-function bound [Hai14, (2.15)] to the
`Q`-form model bound, for a model `M` on `ℝ⁴`, `D = Π_x e_i`, `σ = τ/2`:

* `Model.abs_gammaMap_single_apply_le_ite`:
  `|(Γ_{yx} e_i)_k| ≤ max(1, C_Γ) d(y, x)^{deg i − deg k}` for `deg k ≤ deg i`, and `0` otherwise;
* `Model.regPi_single_eq_sum_gammaMap`: `(Q_s Π_x e_i)(y) = ∑_k (Γ_{wx} e_i)_k (Q_s Π_w e_k)(y)`;
* `Model.abs_regPi_single_le_of_diag`: if `|(Q_σ Π_y e_k)(y)| ≤ B σ^{deg k/4}` for all `y, k`,
  then `|(Q_σ Π_x e_i)(y)| ≤ ∑_{deg k ≤ deg i} max(1, C_Γ) B σ^{deg k/4} d(y, x)^{deg i − deg k}`;
* `Model.abs_regPi_sub_mollify_le` (**mollification error at positive time**): under the same
  hypothesis, for `c ≤ σ^{1/4}`,
  `|D_τ(x) ∫ φ − ∫ φ^c_0(v) D_τ(x + v) dv| ≤ 16 ∑_k max(1, C_Γ) B σ^{deg k/4} K_k (σ^{-1/4} c)
  σ^{(deg i − deg k)/4}`, by the weighted kernel increments of
  `RegularityStructures.Abstract.QFamilyR4KernelIncrement`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

section General

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {𝒯 : RegularityStructure ι}
  {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `(Q_s Π_x e_i)(y) = ∑_k (Γ_{wx} e_i)_k (Q_s Π_w e_k)(y)`. -/
theorem regPi_single_eq_sum_gammaMap (x w : E) (i : ι) (s : ℝ) (y : E) :
    M.regPi x (Pi.single i 1) s y =
      ∑ k, M.gammaMap w x (Pi.single i 1) k * M.regPi w (Pi.single k 1) s y := by
  rw [← M.regPi_gammaMap w x, M.regPi_eq_sum]

/-- The sum of `regPi_single_eq_sum_gammaMap` restricted to `deg k ≤ deg i`. -/
theorem regPi_single_eq_sum_filter_gammaMap (x w : E) (i : ι) (s : ℝ) (y : E) :
    M.regPi x (Pi.single i 1) s y =
      ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
        M.gammaMap w x (Pi.single i 1) k * M.regPi w (Pi.single k 1) s y := by
  rw [M.regPi_single_eq_sum_gammaMap x w i s y]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  have hk' : 𝒯.deg i < 𝒯.deg k := not_le.1 fun h => hk (Finset.mem_filter.2 ⟨Finset.mem_univ k, h⟩)
  have hki : k ≠ i := fun h => by rw [h] at hk'; exact lt_irrefl _ hk'
  rw [M.gammaMap_single_apply_of_le x w hki hk'.le, zero_mul]

end General

end Model

end RegularityStructures

end
