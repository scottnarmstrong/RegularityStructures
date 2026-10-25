/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.LatticeAvg

/-!
# Pointwise convergence of the lattice average

For every `y`, `latticeAvg 𝒯 g γ f n y → R̃f(y) = pointwiseReconstruct g f y` as `n → ∞`
(`tendsto_latticeAvg`).  Outside the slab both sides vanish eventually; at a point `y` of the
slab, the cells containing `y` are centred at lattice points `z` of the slab with
`d(y, z) ≤ 8 · 2^{-n} ≤ min(w_z, w_y)` for large `n`, so the singular increment bound
`abs_fnComb_sub_pointwiseReconstruct_le_of_close` gives
`|latticeAvg n y − R̃f(y)| ≲ ∑_j (8 · 2^{-n})^{γ − deg j} → 0`.

Source: [Hai14] = arXiv:1303.5113v4, Remark 3.15.
-/

public section

open Set Filter Topology

namespace RegularityStructures

theorem tendsto_inv_two_pow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

theorem eventually_inv_two_pow_lt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ n)⁻¹ < δ :=
  tendsto_inv_two_pow.eventually (gt_mem_nhds hδ)

end RegularityStructures
