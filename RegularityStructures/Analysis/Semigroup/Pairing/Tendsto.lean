/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Existence of the pairing

`LocalData.exists_tendsto_integral`: `s ↦ ∫ Λ_s φ` has a limit as `s ↓ 0` (Cauchy criterion
from `LocalData.abs_integral_sub_le`, since the primitive `incrBound` tends to `0`).
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem tendsto_incrBound {A : Finset ℝ} (hA : ∀ a ∈ A, -K.order < a) (γ lam β : ℝ) :
    Tendsto (K.incrBound A γ lam β) (𝓝[>] 0) (𝓝 0) := by
  have hℓ := K.order_pos
  have h : ∀ a ∈ A, Tendsto (fun δ : ℝ => (δ ^ (a / K.order + 1) / (a / K.order + 1)) *
      lam ^ (γ - a)) (𝓝 0) (𝓝 0) := by
    intro a ha
    have hpos : 0 < a / K.order + 1 := by
      have : -1 < a / K.order := by rw [lt_div_iff₀ hℓ]; linarith [hA a ha]
      linarith
    have hc := (((Real.continuous_rpow_const hpos.le).div_const (a / K.order + 1)).mul_const
      (lam ^ (γ - a))).tendsto 0
    rwa [Real.zero_rpow hpos.ne', zero_div, zero_mul] at hc
  have := ((tendsto_finsetSum A h).const_mul β)
  rw [Finset.sum_const_zero, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

end RegularityStructures.RegularisingSemigroup

end
