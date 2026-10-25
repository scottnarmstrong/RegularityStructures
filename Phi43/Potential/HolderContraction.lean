/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.PDE.HeatOpBridge
public import RegularityStructures.Torus.HolderBesov

/-!
# The heat flow contracts the `𝒞^η` norm

`‖P_r g‖_η ≤ ‖g‖_η` for `r > 0` (`holderBesovENorm_heatOp_le`): for each `0 < u ≤ 1` one has
`P_u (P_r g) = P_r (P_u g)` and `P_r` contracts the supremum norm, so the quantity
`sup_x |P_u g (x)|` entering the definition of the norm does not increase.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Potential

open RegularityStructures

theorem iSup_enorm_heatSemigroup_heatOp_le {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 < u)
    (g : C(Torus3, ℝ)) :
    ⨆ x, ‖heatSemigroup u (PDE.heatOp r g) x‖ₑ ≤ ⨆ x, ‖heatSemigroup u g x‖ₑ := by
  refine iSup_le fun x => ?_
  rw [PDE.heatSemigroup_heatOp hr hu g x, add_comm, ← PDE.heatSemigroup_heatOp hu hr g x]
  have h1 : ‖heatSemigroup r (PDE.heatOp u g) x‖ ≤ ‖PDE.heatOp u g‖ :=
    norm_heatSemigroup_le hr _ x
  have h2 : ‖PDE.heatOp u g‖ₑ ≤ ⨆ x, ‖heatSemigroup u g x‖ₑ := by
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    refine iSup_mono fun y => ?_
    rw [PDE.heatOp_eq_heatSemigroup hu]
  exact (enorm_le_iff_norm_le.2 h1).trans h2

/-- **The heat flow contracts the `𝒞^η` norm.** -/
theorem holderBesovENorm_heatOp_le (η : ℝ) {r : ℝ} (hr : 0 < r) (g : C(Torus3, ℝ)) :
    holderBesovENorm η (PDE.heatOp r g) ≤ holderBesovENorm η g := by
  refine iSup₂_le fun u hu => ?_
  exact (mul_le_mul_right (iSup_enorm_heatSemigroup_heatOp_le hr hu.1 g) _).trans
    (le_iSup₂ (f := fun u (_ : u ∈ Ioc (0 : ℝ) 1) =>
      ENNReal.ofReal (u ^ (-η / 2)) * ⨆ x, ‖heatSemigroup u g x‖ₑ) u hu)

/-- The definition of the `𝒞^η` norm gives `‖P_u g‖_∞ ≤ u^{η/2} ‖g‖_η` for `0 < u ≤ 1`. -/
theorem norm_heatOp_le_of_holderBesovENorm_le (η : ℝ) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {g : C(Torus3, ℝ)} {N : ℝ} (hN : 0 ≤ N) (hg : holderBesovENorm η g ≤ ENNReal.ofReal N) :
    ‖PDE.heatOp u g‖ ≤ u ^ (η / 2) * N := by
  have h1 : ENNReal.ofReal (u ^ (-η / 2)) * ‖PDE.heatOp u g‖ₑ ≤ ENNReal.ofReal N := by
    refine le_trans ?_ hg
    refine le_trans (mul_le_mul_right ?_ _)
      (le_iSup₂ (f := fun u (_ : u ∈ Ioc (0 : ℝ) 1) =>
        ENNReal.ofReal (u ^ (-η / 2)) * ⨆ x, ‖heatSemigroup u g x‖ₑ) u hu)
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    refine iSup_mono fun y => ?_
    rw [PDE.heatOp_eq_heatSemigroup hu.1]
  have hp : 0 < u ^ (-η / 2) := Real.rpow_pos_of_pos hu.1 _
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hp.le, ENNReal.ofReal_le_ofReal_iff hN] at h1
  have e : u ^ (η / 2) * u ^ (-η / 2) = 1 := by
    rw [← Real.rpow_add hu.1, show η / 2 + -η / 2 = 0 by ring, Real.rpow_zero]
  calc ‖PDE.heatOp u g‖ = u ^ (η / 2) * (u ^ (-η / 2) * ‖PDE.heatOp u g‖) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ u ^ (η / 2) * N := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hu.1.le _)

end RegularityStructures.Potential

end
