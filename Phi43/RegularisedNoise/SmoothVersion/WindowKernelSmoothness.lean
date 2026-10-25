/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.TimePeriodise
public import Phi43.RegularisedNoise.SmoothVersion.WindowKernelRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth slices of the finite-window translated kernel

The finite-window torus representative is continuous by `SmoothVersionWindowKernelRegularity`.
This module supplies the stronger slice regularity needed by the coordinatewise integration-by-
parts estimate.  Time is handled by periodising the translated kernel before taking the quotient;
spatial slices are ordinary smooth periodic lifts.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace RegularityStructures.Phi43

def windowKernelRaw (Phi : SpaceTime → ℝ) (z : SpaceTime) (a b : ℝ)
    (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  Phi (z - (a + (b - a) * p.1, torusProj p.2))

private theorem torusProj_sub_torusRep_raw (x : Torus3) (y : Fin 3 → ℝ) :
    torusProj (torusRep x - y) = x - torusProj y := by
  ext i
  change ((torusRep x i - y i : ℝ) : UnitAddCircle) = x i - (y i : UnitAddCircle)
  change ((torusRep x i : UnitAddCircle) - (y i : UnitAddCircle)) =
    x i - (y i : UnitAddCircle)
  rw [show ((torusRep x i : ℝ) : UnitAddCircle) = x i by
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x i)]

private theorem torusProj_torusRep_window (x : Torus3) :
    torusProj (torusRep x) = x := by
  ext i
  dsimp [torusProj, torusRep]
  exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x i)

theorem contDiff_windowKernelRaw
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    (z : SpaceTime) (a b : ℝ) :
    ContDiff ℝ ∞ (windowKernelRaw Phi z a b) := by
  unfold windowKernelRaw
  let g : (ℝ × (Fin 3 → ℝ)) → (ℝ × (Fin 3 → ℝ)) := fun p =>
    (z.1 - (a + (b - a) * p.1), torusRep z.2 - p.2)
  have hg : ContDiff ℝ ∞ g := by
    fun_prop
  have hcomp := hPhi.comp hg
  have heq : (fun p : ℝ × (Fin 3 → ℝ) =>
      Phi (z - (a + (b - a) * p.1, torusProj p.2))) =
      (fun p : ℝ × (Fin 3 → ℝ) =>
        Phi (z.1 - (a + (b - a) * p.1),
          torusProj (torusRep z.2 - p.2))) := by
    funext p
    change Phi (z.1 - (a + (b - a) * p.1), z.2 - torusProj p.2) = _
    rw [torusProj_sub_torusRep_raw]
  rw [heq]
  exact hcomp

theorem windowKernelLift_eq_timePeriodise
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (hR0 : 0 ≤ R) (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1) (x : Torus3) (s : ℝ) :
    windowKernelLift Phi hPhi z a b hends
        (coordinateInsert 0 (s : UnitAddCircle) x) =
      timePeriodise (fun q : SpaceTime =>
        Phi (z - (a + (b - a) * q.1, q.2))) 1 (s, torusRep x) := by
  let H : SpaceTime → ℝ := fun q =>
    Phi (z - (a + (b - a) * q.1, q.2))
  let S : ℝ := (R + |z.1 - a| + 1) / (b - a)
  let g : ℝ → ℝ := fun t => timePeriodise H 1 (t, torusRep x)
  have hL : 0 < b - a := by
    rw [ha, hb]
    have hN : 0 < N := lt_of_le_of_lt (abs_nonneg z.1) hz
    linarith
  have hsupport : ∀ q : SpaceTime, S < |q.1| → H q = 0 := by
    intro q hq
    apply hR
    change R < |z.1 - (a + (b - a) * q.1)|
    have hdist : R + |z.1 - a| + 1 < (b - a) * |q.1| := by
      simpa [S, mul_comm] using (div_lt_iff₀ hL).mp hq
    have habs : (b - a) * |q.1| ≤ |(b - a) * q.1| := by
      rw [abs_mul, abs_of_pos hL]
    have hlarge : R + |z.1 - a| + 1 < |(b - a) * q.1| := hdist.trans_le habs
    have htriangle : |(b - a) * q.1| ≤
        |z.1 - (a + (b - a) * q.1)| + |z.1 - a| := by
      calc
        |(b - a) * q.1| =
            |(z.1 - a) - (z.1 - (a + (b - a) * q.1))| := by
              congr 1
              ring
        _ ≤ _ := by
          simpa [abs_zero, abs_neg, abs_sub_comm, add_comm] using
            (abs_sub_le (z.1 - a) 0
              (z.1 - (a + (b - a) * q.1)))
    linarith
  have hH : IsSmoothOnSpaceTime H := by
    unfold IsSmoothOnSpaceTime
    change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      Phi (z - (a + (b - a) * p.1, torusProj p.2)))
    exact contDiff_windowKernelRaw hPhi z a b
  have hper : Function.Periodic g 1 := by
    intro t
    simpa [g] using
      (timePeriodise_add_period (Phi := H) (L := (1 : ℝ)) one_ne_zero
        (t, torusRep x))
  have hsingle : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ n : ℤ, n ≠ 0 →
      H (t + (n : ℝ), x) = 0 := by
    intro t ht n hn
    have hncases : n < 0 ∨ 0 < n := by omega
    rcases hncases with hnneg | hnpos
    · have hnle : (n : ℝ) ≤ -1 := by
        have : n ≤ -1 := by omega
        exact_mod_cast this
      have htn : t + (n : ℝ) ≤ 0 := by linarith [ht.2]
      have hu : a + (b - a) * (t + (n : ℝ)) ≤ a := by
        have hmul : (b - a) * (t + (n : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hL.le htn
        linarith
      have hzlow : -N < z.1 := (abs_lt.mp hz).1
      have htime : R < |z.1 - (a + (b - a) * (t + (n : ℝ)))| := by
        have hu' : a + (b - a) * (t + (n : ℝ)) ≤ -N - R - 1 := by
          simpa [ha] using hu
        have hneg : 0 < z.1 - (a + (b - a) * (t + (n : ℝ))) := by
          linarith
        rw [abs_of_pos hneg]
        linarith [hu', hzlow]
      exact hR _ htime
    · have hnge : (1 : ℝ) ≤ n := by
        have : (1 : ℤ) ≤ n := by omega
        exact_mod_cast this
      have htn : 1 ≤ t + (n : ℝ) := by linarith [ht.1]
      have hu : b ≤ a + (b - a) * (t + (n : ℝ)) := by
        have hmul : b - a ≤ (b - a) * (t + (n : ℝ)) := by
          nlinarith [hL]
        linarith
      have hzupper : z.1 < N := (abs_lt.mp hz).2
      have htime : R < |z.1 - (a + (b - a) * (t + (n : ℝ)))| := by
        have hu' : N + R + 1 ≤ a + (b - a) * (t + (n : ℝ)) := by
          simpa [hb] using hu
        have hneg : z.1 - (a + (b - a) * (t + (n : ℝ))) < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith [hu', hzupper]
      exact hR _ htime
  have hfg : ∀ t ∈ Ioc (0 : ℝ) 1,
      windowKernelTimeMap Phi hPhi z a b t x = g t := by
    intro t ht
    unfold g H timePeriodise
    rw [tsum_eq_single 0]
    · simp [windowKernelTimeMap, torusProj_torusRep_window]
    · intro n hn
      simpa [torusProj_torusRep_window] using hsingle t ht n hn
  have hlift := liftIoc_eq_periodic_lift_of_eq_on_Ioc hper hfg
  change (AddCircle.liftIoc (1 : ℝ) 0
      (windowKernelTimeMap Phi hPhi z a b) (s : UnitAddCircle)) x = g s
  calc
    _ = AddCircle.liftIoc (1 : ℝ) 0
        (fun t => windowKernelTimeMap Phi hPhi z a b t x)
        (s : UnitAddCircle) := by
      exact (AddCircle.liftIoc_comp_apply
        (f := windowKernelTimeMap Phi hPhi z a b)
        (g := fun F : C(Torus3, ℝ) => F x)
        (a := (0 : ℝ)) (x := (s : UnitAddCircle))).symm
    _ = hper.lift (s : UnitAddCircle) := by rw [hlift]
    _ = g s := hper.lift_coe s

theorem contDiff_windowKernelLift_realLift
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (hR0 : 0 ≤ R) (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      windowKernelLift Phi hPhi z a b hends
        (coordinateInsert 0 (p.1 : UnitAddCircle)
          (fun i => ((p.2 i : ℝ) : UnitAddCircle)))) := by
  let H : SpaceTime → ℝ := fun q =>
    Phi (z - (a + (b - a) * q.1, q.2))
  have hL : 0 < b - a := by
    rw [ha, hb]
    have hN : 0 < N := lt_of_le_of_lt (abs_nonneg z.1) hz
    linarith
  have hsupport : ∀ q : SpaceTime,
      (R + |z.1 - a| + 1) / (b - a) < |q.1| → H q = 0 := by
    intro q hq
    apply hR
    change R < |z.1 - (a + (b - a) * q.1)|
    have hdist : R + |z.1 - a| + 1 < (b - a) * |q.1| := by
      simpa [mul_comm] using (div_lt_iff₀ hL).mp hq
    have habs : (b - a) * |q.1| ≤ |(b - a) * q.1| := by
      rw [abs_mul, abs_of_pos hL]
    have htriangle : |(b - a) * q.1| ≤
        |z.1 - (a + (b - a) * q.1)| + |z.1 - a| := by
      calc
        |(b - a) * q.1| =
            |(z.1 - a) - (z.1 - (a + (b - a) * q.1))| := by
              congr 1
              ring
        _ ≤ _ := by
          simpa [abs_zero, abs_neg, abs_sub_comm, add_comm] using
            (abs_sub_le (z.1 - a) 0
              (z.1 - (a + (b - a) * q.1)))
    linarith
  have hH : IsSmoothOnSpaceTime H := by
    unfold IsSmoothOnSpaceTime
    change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      Phi (z - (a + (b - a) * p.1, torusProj p.2)))
    exact contDiff_windowKernelRaw hPhi z a b
  have hg : ContDiff ℝ ∞ (timePeriodise H 1) :=
    contDiff_timePeriodise hH hsupport (by norm_num)
  have hEq : (fun p : ℝ × (Fin 3 → ℝ) =>
      windowKernelLift Phi hPhi z a b hends
        (coordinateInsert 0 (p.1 : UnitAddCircle)
          (fun i => ((p.2 i : ℝ) : UnitAddCircle)))) =
      timePeriodise H 1 := by
    funext p
    rw [windowKernelLift_eq_timePeriodise hPhi hR hz hR0 ha hb hends
      (fun i => ((p.2 i : ℝ) : UnitAddCircle)) p.1]
    unfold timePeriodise
    apply tsum_congr
    intro n
    congr 2
    rw [torusProj_torusRep_window]
    rfl
  rw [hEq]
  exact hg

end RegularityStructures.Phi43

end
