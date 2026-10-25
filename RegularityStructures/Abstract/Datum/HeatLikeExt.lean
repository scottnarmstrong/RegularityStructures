/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.HeatField
public import RegularityStructures.Abstract.Datum.HeatExt
public import RegularityStructures.Abstract.Datum.HeatBounds

/-!
# The heat field of an initial datum in `𝒞^η`

`datumField η a (t, y) = P_t a (y)` for `t > 0` (and `0` otherwise). For `0 < s < t` it equals
`heatField (P_s a) (t - s, y)` (semigroup law), so it inherits smoothness, the heat equation and
the spatial derivative bounds from `HeatField`. Choosing `s = t/2` and using
`‖P_{t/2} a‖_∞ ≤ (t/2)^{η/2} ‖a‖_η` gives
`|∂_w datumField (t, y)| ≤ K_m ‖a‖_η t^{(η - m)/2}` for `0 < t ≤ 1` (`heatLike_datumField`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The shift `(t, y) ↦ (t - s, y)` in time. -/
def shiftT (s : ℝ) (z : ParabolicSpace) : ParabolicSpace := (z.1 - s, z.2)

/-- `datumField η a (t, y) = P_t a (y)` for `t > 0`, and `0` for `t ≤ 0`. -/
def datumField (η : NegExponent) (a : HolderBesov η) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then heatExt η a z.1 (torusProj z.2) else 0

end RegularityStructures.Datum

end

public section

open Set Filter Topology
open scoped ContDiff

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem shiftT_eq_sub (s : ℝ) (z : ParabolicSpace) : shiftT s z = z - (s, 0) := by
  ext <;> simp [shiftT]

theorem pdv_congr_on {U : Set ParabolicSpace} (hU : IsOpen U) {v : ParabolicSpace}
    {F G : ParabolicSpace → ℝ} (h : ∀ z ∈ U, F z = G z) : ∀ z ∈ U, pdv v F z = pdv v G z := by
  intro z hz
  by_cases hz0 : 0 < z.1
  · rw [pdv_of_pos hz0, pdv_of_pos hz0]
    have : F =ᶠ[nhds z] G := Filter.eventually_of_mem (hU.mem_nhds hz) h
    rw [this.fderiv_eq]
  · rw [pdv_of_nonpos (not_lt.1 hz0), pdv_of_nonpos (not_lt.1 hz0)]

theorem pdWord_congr_on {U : Set ParabolicSpace} (hU : IsOpen U) {F G : ParabolicSpace → ℝ}
    (h : ∀ z ∈ U, F z = G z) (w : List (Fin 3)) : ∀ z ∈ U, pdWord w F z = pdWord w G z := by
  induction w with
  | nil => exact h
  | cons j w ih => exact pdv_congr_on hU ih

theorem pdv_comp_shift (G : ParabolicSpace → ℝ) (v : ParabolicSpace) {s : ℝ} (hs : 0 ≤ s)
    {z : ParabolicSpace} (hz : s < z.1) :
    pdv v (fun p => G (shiftT s p)) z = pdv v G (shiftT s z) := by
  have hz0 : 0 < z.1 := lt_of_le_of_lt hs hz
  have hz1 : 0 < (shiftT s z).1 := sub_pos.2 hz
  rw [pdv_of_pos hz0, pdv_of_pos hz1]
  have e : (fun p => G (shiftT s p)) = fun p => G (p - (s, 0)) := by
    funext p; rw [shiftT_eq_sub]
  rw [e, fderiv_comp_sub, ← shiftT_eq_sub]

theorem pdWord_comp_shift {G : ParabolicSpace → ℝ} {s : ℝ} (hs : 0 ≤ s) (w : List (Fin 3)) :
    ∀ z : ParabolicSpace, s < z.1 →
      pdWord w (fun p => G (shiftT s p)) z = pdWord w G (shiftT s z) := by
  induction w with
  | nil => intro z _; rfl
  | cons j w ih =>
    intro z hz
    have hU : IsOpen {p : ParabolicSpace | s < p.1} := isOpen_lt continuous_const continuous_fst
    have h1 := pdv_congr_on hU (v := stBasis j.succ) (fun p hp => ih p hp) z hz
    show pdv (stBasis j.succ) (pdWord w fun p => G (shiftT s p)) z = _
    rw [h1, pdv_comp_shift (pdWord w G) _ hs hz]
    rfl

theorem datumField_of_pos (η : NegExponent) (a : HolderBesov η) {z : ParabolicSpace}
    (hz : 0 < z.1) : datumField η a z = heatExt η a z.1 (torusProj z.2) := by
  simp [datumField, hz]

/-- The semigroup law in space-time form. -/
theorem datumField_eq_heatField (η : NegExponent) (a : HolderBesov η) {s : ℝ} (hs : 0 < s)
    {z : ParabolicSpace} (hz : s < z.1) :
    datumField η a z = heatField (heatExt η a s) (shiftT s z) := by
  have hz0 : 0 < z.1 := hs.trans hz
  have hz1 : 0 < (shiftT s z).1 := sub_pos.2 hz
  rw [datumField_of_pos η a hz0, heatField_of_pos _ hz1]
  have := heatOp_heatExt η a (sub_pos.2 hz) hs
  rw [sub_add_cancel] at this
  show _ = heatOp (z.1 - s) (heatExt η a s) (torusProj z.2)
  rw [this]

theorem smoothPos_datumField (η : NegExponent) (a : HolderBesov η) :
    SmoothPos (datumField η a) := by
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  have hz0 : 0 < z.1 := hz
  set s : ℝ := z.1 / 2 with hs
  have hs0 : 0 < s := half_pos hz0
  refine ⟨{p | s < p.1}, isOpen_lt continuous_const continuous_fst, by simp [hs]; linarith, ?_⟩
  have hρ : ContDiffOn ℝ ∞ (shiftT s) (posTime ∩ {p | s < p.1}) :=
    (ContDiff.contDiffOn ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd))
  refine ((smoothPos_heatField (heatExt η a s)).comp hρ ?_).congr ?_
  · intro p hp
    exact sub_pos.2 hp.2
  · intro p hp
    exact datumField_eq_heatField η a hs0 hp.2

theorem pdWord_datumField (η : NegExponent) (a : HolderBesov η) {s : ℝ} (hs : 0 < s)
    (w : List (Fin 3)) {z : ParabolicSpace} (hz : s < z.1) :
    pdWord w (datumField η a) z = pdWord w (heatField (heatExt η a s)) (shiftT s z) := by
  have hU : IsOpen {p : ParabolicSpace | s < p.1} := isOpen_lt continuous_const continuous_fst
  rw [pdWord_congr_on hU (G := fun p => heatField (heatExt η a s) (shiftT s p))
    (fun p hp => datumField_eq_heatField η a hs hp) w z hz]
  exact pdWord_comp_shift hs.le w z hz

theorem heatEq_datumField (η : NegExponent) (a : HolderBesov η) : HeatEq (datumField η a) := by
  funext z
  by_cases hz : 0 < z.1
  · set s : ℝ := z.1 / 2 with hs
    have hs0 : 0 < s := half_pos hz
    have hsz : s < z.1 := by linarith
    have hU : IsOpen {p : ParabolicSpace | s < p.1} := isOpen_lt continuous_const continuous_fst
    set g := heatExt η a s with hg
    have hL : pd 0 (datumField η a) z = pd 0 (heatField g) (shiftT s z) := by
      have h1 := pdv_congr_on hU (v := stBasis 0) (G := fun p => heatField g (shiftT s p))
        (fun p hp => datumField_eq_heatField η a hs0 hp) z hsz
      show pdv (stBasis 0) _ z = pdv (stBasis 0) _ _
      rw [h1]
      exact pdv_comp_shift _ _ hs0.le hsz
    have hR : ∀ j : Fin 3, pd j.succ (pd j.succ (datumField η a)) z =
        pd j.succ (pd j.succ (heatField g)) (shiftT s z) := fun j =>
      pdWord_datumField η a hs0 [j, j] hsz
    have hH := congrFun (heatEq_heatField g) (shiftT s z)
    show pd 0 (datumField η a) z = (∑ j : Fin 3, pd j.succ (pd j.succ (datumField η a))) z
    rw [Finset.sum_apply, hL]
    rw [Finset.sum_apply] at hH
    rw [hH]
    exact Finset.sum_congr rfl fun j _ => (hR j).symm
  · simp [pd, pdv, hz]

theorem spatialBound_datumField (η : NegExponent) :
    SpatialBound (η : ℝ) (fun a : HolderBesov η => ‖a‖) (datumField η) := by
  intro m
  obtain ⟨K, hK0, hK⟩ := abs_pdWord_heatField_le m
  refine ⟨K / (2 : ℝ) ^ (((η : ℝ) - m) / 2), fun a w hw z hz hz1 => ?_⟩
  set s : ℝ := z.1 / 2 with hs
  have hs0 : 0 < s := half_pos hz
  have hsz : s < z.1 := by linarith
  have hs1 : s ≤ 1 := by linarith
  rw [pdWord_datumField η a hs0 w hsz]
  have hz' : 0 < (shiftT s z).1 := sub_pos.2 hsz
  have h1 := hK (heatExt η a s) w hw (shiftT s z) hz'
  have hts : (shiftT s z).1 = z.1 / 2 := by simp [shiftT, hs]; ring
  rw [hts] at h1
  have h2 := norm_heatExt_le η a hs0
  rw [min_eq_left hs1] at h2
  refine h1.trans ?_
  have hz2 : 0 < z.1 / 2 := half_pos hz
  have e1 : (z.1 / 2) ^ (-(m : ℝ) / 2) * s ^ ((η : ℝ) / 2) = (z.1 / 2) ^ (((η : ℝ) - m) / 2) := by
    rw [← Real.rpow_add hz2]
    congr 1
    ring
  have e2 : (z.1 / 2) ^ (((η : ℝ) - m) / 2) = z.1 ^ (((η : ℝ) - m) / 2) / (2 : ℝ) ^ (((η : ℝ) - m) / 2) :=
    Real.div_rpow hz.le (by norm_num) _
  calc K * (z.1 / 2) ^ (-(m : ℝ) / 2) * ‖heatExt η a s‖
      ≤ K * (z.1 / 2) ^ (-(m : ℝ) / 2) * (s ^ ((η : ℝ) / 2) * ‖a‖) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 (Real.rpow_nonneg hz2.le _))
    _ = K * ((z.1 / 2) ^ (-(m : ℝ) / 2) * s ^ ((η : ℝ) / 2)) * ‖a‖ := by ring
    _ = K / (2 : ℝ) ^ (((η : ℝ) - m) / 2) * ‖a‖ * z.1 ^ (((η : ℝ) - m) / 2) := by
        rw [e1, e2]
        ring

/-- **The heat field of `a ∈ 𝒞^η` is a smooth solution of the heat equation with the spatial
bounds `O(‖a‖_η t^{(η - m)/2})`.** -/
theorem heatLike_datumField (η : NegExponent) :
    HeatLike (η : ℝ) (fun a : HolderBesov η => ‖a‖) (datumField η) :=
  ⟨smoothPos_datumField η, heatEq_datumField η, spatialBound_datumField η⟩

end RegularityStructures.Datum

end
