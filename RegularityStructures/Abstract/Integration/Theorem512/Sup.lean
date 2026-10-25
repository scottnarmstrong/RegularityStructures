/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.RegularityStructure

/-!
# Sup bounds and degree support of `𝒦_γ f`

For `f ∈ D^γ` with values in the sector `V` and a `SchauderSetting`:

* `Model.abs_kGamma_apply_le_of_notMem_range`: `|𝒦_γ f(x)_j| ≤ |ι| C_I C_f` for `j ∉ range P.emb`;
* `Model.abs_kGamma_apply_emb_le`: `|𝒦_γ f(x)_{X^k}| ≤ c_k C_Π max(C_Γ, 1) C_f` for
  `|k|_𝔰 < γ + 2`, with `c_k = supConst 𝒯 γ N k` independent of the model and of `f`
  (from `abs_jCoeff_le` and `abs_nCoeff_le`);
* `Model.kGamma_mem_lowerSubspace`: `𝒦_γ f(x) ∈ T_{<γ+2}` (`I` raises degrees by `2`; `J`, `N_γ`
  only use `|k|_𝔰 < γ + 2`).

Source: [Hai14] = arXiv:1303.5113v4, Theorem 5.12.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem linearMap_apply_eq_sum (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (τ : ι → ℝ) (j : ι) :
    I τ j = ∑ i, τ i * I (Pi.single i 1) j := by
  conv_lhs => rw [eq_sum_single τ]
  simp [map_sum, Finset.sum_apply]

end RegularityStructures

end
