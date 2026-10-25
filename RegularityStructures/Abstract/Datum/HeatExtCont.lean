/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.HeatExt

/-!
# Strong continuity of the heat semigroup on `𝒞^η`

`P_t` contracts the `η`-norm (`holderBesovENorm_heatOp_le`), and `P_t f → f` in `C(T³)`, hence in
`𝒞^η`, as `t ↓ 0`. By density and the uniform bound, `P_t a → a` in `𝒞^η` for every `a ∈ 𝒞^η`
(`tendsto_heatExt_nhdsGT`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem iSup_enorm_heatSemigroup (f : C(Torus3, ℝ)) {s : ℝ} (hs : 0 < s) :
    ⨆ x, ‖heatSemigroup s f x‖ₑ = ‖heatOp s f‖ₑ := by
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  exact iSup_congr fun x => by rw [heatOp_eq_heatSemigroup hs]

/-- `P_t` is a contraction for `‖·‖_η`. -/
theorem holderBesovENorm_heatOp_le (η : NegExponent) {t : ℝ} (ht : 0 < t) (f : C(Torus3, ℝ)) :
    holderBesovENorm η (heatOp t f) ≤ holderBesovENorm η f := by
  refine iSup₂_le fun s hs => ?_
  refine le_iSup₂_of_le s hs (mul_le_mul_right ?_ _)
  rw [iSup_enorm_heatSemigroup _ hs.1, iSup_enorm_heatSemigroup _ hs.1]
  have e : heatOp s (heatOp t f) = heatOp t (heatOp s f) := by
    rw [heatOp_heatOp ht.le hs.1.le, heatOp_heatOp hs.1.le ht.le, add_comm]
  rw [e]
  exact enorm_le_iff_norm_le.2 (norm_heatOp_le _ _)

end RegularityStructures.Datum

end
