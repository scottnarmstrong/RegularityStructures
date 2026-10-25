/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSCompactNet
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Topological convergence of intrinsic compact nets

Hairer--Steele, arXiv:2301.10081v3, Proposition B.3: the occupied-cell
approximants converge in the original space-time topology. In particular,
any continuous version is determined by its values at the countable
union of these finite nets.
-/

public section

open Filter
open scoped Topology

namespace RegularityStructures

/-- The ordinary product distance between a point and its cell representative is small. -/
theorem hsParabolicCellApprox_dist_le (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : S) :
    dist (hsParabolicCellApprox S n x) x ≤ 1 / (2 : ℝ) ^ n := by
  let y := hsParabolicCellApprox S n x
  have hx := hbox _ x.property
  have hy := hbox _ y.property
  have h := hsParabolicCellApprox_index S n x
  have ht := hsDyadicCellIndex_abs_sub_le (2 * n)
    ⟨(y : ParabolicSpace).1, hy.1⟩ ⟨(x : ParabolicSpace).1, hx.1⟩ (congrArg Prod.fst h)
  have hs (j : Fin 3) := hsDyadicCellIndex_abs_sub_le n
    ⟨(y : ParabolicSpace).2 j, hy.2 j⟩ ⟨(x : ParabolicSpace).2 j, hx.2 j⟩
      (congrFun (congrArg Prod.snd h) j)
  have hscale : 1 / (2 : ℝ) ^ (2 * n) ≤ 1 / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  change max (dist (y : ParabolicSpace).1 (x : ParabolicSpace).1)
    (dist (y : ParabolicSpace).2 (x : ParabolicSpace).2) ≤ _
  apply max_le
  · simpa only [Real.dist_eq] using ht.trans hscale
  · exact (dist_pi_le_iff (by positivity)).2 fun j => by
      simpa only [Real.dist_eq] using hs j

/-- Intrinsic cell representatives converge to the point in the original topology. -/
theorem hsParabolicCellApprox_tendsto (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (x : S) : Tendsto (fun n => hsParabolicCellApprox S n x) atTop (𝓝 x) := by
  have hbase : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num))
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => hsParabolicCellApprox_dist_le S hbox n x) hbase

end RegularityStructures

end
