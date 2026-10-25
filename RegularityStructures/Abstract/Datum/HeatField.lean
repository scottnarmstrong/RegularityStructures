/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.HeatFlow
public import RegularityStructures.Abstract.Datum.HeatBounds

/-!
# The space-time heat field of a continuous function

For `g ∈ C(T³)`, `heatField g (t, y) = P_t g (y)` for `t > 0` (and `0` otherwise). It is smooth on
`{t > 0}` (`smoothPos_heatField`: for `s > 0` and `t > s` it is the heat flow of the smooth
function `P_s g`, shifted by `s` in time), solves the heat equation (`heatEq_heatField`), and
its spatial derivatives satisfy `|∂_w heatField g (t, y)| ≤ K_m t^{-m/2} ‖g‖`
(`abs_pdWord_heatField_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- `heatField g (t, y) = P_t g (y)` for `t > 0`, and `0` for `t ≤ 0`. -/
def heatField (g : C(Torus3, ℝ)) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then heatOp z.1 g (torusProj z.2) else 0

end RegularityStructures.Datum

end

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem stBasis_succ (j : Fin 3) : stBasis j.succ = (0, Pi.single j 1) := by
  ext k
  · simp [stBasis, stOfCoords, Pi.single_apply, Fin.succ_ne_zero]
  · simp [stBasis, stOfCoords, Pi.single_apply, Fin.succ_inj]

theorem sdLift_slice {F : ParabolicSpace → ℝ} {t : ℝ} {y : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F (t, y)) (j : Fin 3) :
    sdLift j (fun y' => F (t, y')) y = fderiv ℝ F (t, y) (stBasis j.succ) := by
  have hι : HasFDerivAt (fun y' : Fin 3 → ℝ => ((t, y') : ParabolicSpace))
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) y := (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h := (hF.hasFDerivAt.comp y hι).fderiv
  rw [sdLift]
  have e : (fun y' => F (t, y')) = F ∘ fun y' : Fin 3 → ℝ => ((t, y') : ParabolicSpace) := rfl
  rw [e, h, stBasis_succ]
  simp

theorem slice_pdWord {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (w : List (Fin 3)) {t : ℝ}
    (ht : 0 < t) :
    (fun y => pdWord w F (t, y)) = sdWord w (fun y => F (t, y)) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext y
    have hd : DifferentiableAt ℝ (pdWord w F) (t, y) := (hF.pdWord w).differentiableAt ht
    have h1 : pdWord (j :: w) F (t, y) = fderiv ℝ (pdWord w F) (t, y) (stBasis j.succ) := by
      show pd j.succ (pdWord w F) (t, y) = _
      exact pdv_of_pos ht
    rw [h1, ← sdLift_slice hd, ih]
    rfl

theorem stBasis_zero : stBasis 0 = (1, 0) := by
  ext k
  · simp [stBasis, stOfCoords]
  · simp [stBasis, stOfCoords, Fin.succ_ne_zero]

theorem heatOp_shift {g : C(Torus3, ℝ)} {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    heatOp t g = heatOp (t - s) (heatOp s g) := by
  rw [heatOp_heatOp hs.le (sub_pos.2 hst).le, add_sub_cancel]

theorem heatField_of_pos (g : C(Torus3, ℝ)) {z : ParabolicSpace} (hz : 0 < z.1) :
    heatField g z = heatOp z.1 g (torusProj z.2) := by
  simp [heatField, hz]

theorem smoothPos_heatField (g : C(Torus3, ℝ)) : SmoothPos (heatField g) := by
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  have hz0 : 0 < z.1 := hz
  set s : ℝ := z.1 / 2 with hs
  have hs0 : 0 < s := half_pos hz0
  set w : C(Torus3, ℝ) := heatOp s g with hw
  have hwsm : ContDiff ℝ ∞ (liftFn w) := contDiff_lift_heatOp_infty g hs0
  refine ⟨{p | s < p.1 ∧ p.1 < z.1 + 1}, ?_, ⟨by simp [hs]; linarith, by simp⟩, ?_⟩
  · exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  · have hF := contDiffOn_heatFlow hwsm (T := z.1 + 1) (by linarith)
    have hρ : ContDiffOn ℝ ∞ (fun p : ParabolicSpace => ((p.1 - s, p.2) : ℝ × (Fin 3 → ℝ)))
        (posTime ∩ {p | s < p.1 ∧ p.1 < z.1 + 1}) := by
      refine (ContDiff.contDiffOn ?_)
      exact (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    refine (hF.comp hρ ?_).congr ?_
    · intro p hp
      exact ⟨⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩, mem_univ _⟩
    · intro p hp
      have hp1 : s < p.1 := hp.2.1
      rw [heatField_of_pos g hp.1, heatOp_shift hs0 hp1]
      rfl

theorem slice_heatField (g : C(Torus3, ℝ)) {t : ℝ} (ht : 0 < t) :
    (fun y => heatField g (t, y)) = liftFn (heatOp t g) := by
  funext y
  simp [heatField, ht, liftFn]

theorem sdLift_sdLift_heatFlow {u : C(Torus3, ℝ)} {u₁ : C(Torus3, Fin 3 → ℝ)}
    {u₂ : C(Torus3, Fin 3 → Fin 3 → ℝ)} (h1 : HasTorusDeriv u u₁)
    (h2 : HasTorusDeriv (E := Fin 3 → ℝ) u₁ u₂) (j : Fin 3) (y : Fin 3 → ℝ) :
    sdLift j (sdLift j (liftFn u)) y = u₂ (torusProj y) j j := by
  have e1 : sdLift j (liftFn u) = fun y => u₁ (torusProj y) j := by
    funext y
    show fderiv ℝ (fun y => u (torusProj y)) y (Pi.single j 1) = _
    rw [(h1 y).fderiv, ofPartials_single]
  rw [e1]
  have hc : HasFDerivAt (fun y => u₁ (torusProj y) j)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
        (ofPartials (u₂ (torusProj y)))) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp y (h2 y)
  simp only [sdLift, hc.fderiv, ContinuousLinearMap.comp_apply, ofPartials_single]
  rfl

theorem heatEq_heatField (g : C(Torus3, ℝ)) : HeatEq (heatField g) := by
  funext ⟨t, y⟩
  by_cases hz : 0 < t
  · have hsm := smoothPos_heatField g
    set s : ℝ := t / 2 with hs
    have hs0 : 0 < s := half_pos hz
    have hst : s < t := by linarith
    have hτ : 0 < t - s := by linarith
    have hwsm : ContDiff ℝ ∞ (liftFn (heatOp s g)) := contDiff_lift_heatOp_infty g hs0
    obtain ⟨w₁, w₂, h1, h2, h3⟩ := heatFlow_deriv hwsm (T := t + 1) (by linarith)
    have hτT : t - s ∈ Ioo 0 (t + 1) := ⟨hτ, by linarith⟩
    have hτI : t - s ∈ Icc 0 (t + 1) := Ioo_subset_Icc_self hτT
    -- the time derivative
    have hdt : HasDerivAt (fun τ' : ℝ => heatField g (τ', y))
        (torusLap (w₂ (t - s)) (torusProj y)) t := by
      have h4 := HasDerivAt.comp_sub_const t s (h3 (t - s) hτT (torusProj y))
      refine h4.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hst] with τ' hτ'
      have hτ'0 : 0 < τ' := hs0.trans hτ'
      rw [heatField_of_pos g hτ'0, heatOp_shift hs0 hτ']
    have hline : HasDerivAt (fun τ' : ℝ => ((τ', y) : ParabolicSpace)) ((1, 0) : ParabolicSpace) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have hdt' := ((smoothPos_heatField g).differentiableAt (z := (t, y)) hz).hasFDerivAt.comp_hasDerivAt
      t hline
    have hL : pd 0 (heatField g) (t, y) = torusLap (w₂ (t - s)) (torusProj y) := by
      show pdv (stBasis 0) (heatField g) (t, y) = _
      rw [pdv_of_pos hz, stBasis_zero]
      exact hdt'.unique hdt
    -- the spatial second derivatives
    have hR : ∀ j : Fin 3, pd j.succ (pd j.succ (heatField g)) (t, y) =
        w₂ (t - s) (torusProj y) j j := by
      intro j
      have e := congrFun (slice_pdWord hsm [j, j] hz) y
      have e2 : pdWord [j, j] (heatField g) = pd j.succ (pd j.succ (heatField g)) := rfl
      rw [e2] at e
      rw [e]
      simp only [sdWord]
      rw [slice_heatField g hz, heatOp_shift hs0 hst]
      exact sdLift_sdLift_heatFlow (h1 (t - s) hτI) (h2 (t - s) hτI) j y
    show pd 0 (heatField g) (t, y) = (∑ j : Fin 3, pd j.succ (pd j.succ (heatField g))) (t, y)
    rw [Finset.sum_apply, hL, torusLap_apply]
    exact Finset.sum_congr rfl fun j _ => (hR j).symm
  · simp [pd, pdv, hz]

theorem inv_sqrt_pow_eq {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ((√t)⁻¹) ^ m = t ^ (-(m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- The spatial derivatives of `P_t g` are `O(t^{-m/2} ‖g‖)`, with a constant independent of `g`. -/
theorem abs_pdWord_heatField_le (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : C(Torus3, ℝ)) (w : List (Fin 3)), w.length = m →
      ∀ z : ParabolicSpace, 0 < z.1 →
        |pdWord w (heatField g) z| ≤ K * z.1 ^ (-(m : ℝ) / 2) * ‖g‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_sdWord_heatOp m
  refine ⟨K, hK0, fun g w hw ⟨t, y⟩ ht => ?_⟩
  have hsm := smoothPos_heatField g
  have e := congrFun (slice_pdWord hsm w ht) y
  rw [e, slice_heatField g ht]
  obtain ⟨g'', hg'', hn⟩ := hK w hw g ht
  rw [hg'']
  have h1 : |liftFn (heatOp (t / 2 ^ m) g'') y| ≤ ‖g''‖ := by
    have := norm_heatOp_apply_le (t / 2 ^ m) g'' (torusProj y)
    rwa [Real.norm_eq_abs] at this
  refine h1.trans (hn.trans ?_)
  rw [inv_sqrt_pow_eq ht]

end RegularityStructures.Datum

end
