/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowedKernel
public import Phi43.RegularisedNoise.SmoothVersion.CoordinateFourier
public import Phi43.ClassicalSolution.ExistenceCutoff
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Continuity of a finite-window torus kernel

The time coordinate of a finite-window Fourier expansion is represented by an `AddCircle` lift.
The endpoint equality needed by that lift is supplied by vanishing of the translated kernel near
the two ends of the window.  This module isolates that quotient-continuity step.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem liftIoc_eq_periodic_lift_of_eq_on_Ioc
    {f g : ℝ → ℝ} (hper : Function.Periodic g 1)
    (hfg : ∀ t ∈ Ioc (0 : ℝ) 1, f t = g t) :
    AddCircle.liftIoc (1 : ℝ) 0 f = hper.lift := by
  funext y
  rcases AddCircle.eq_coe_Ioc y with ⟨t, ht, hty⟩
  rw [← hty, AddCircle.liftIoc_coe_apply (by simpa using ht), hper.lift_coe]
  exact hfg t ht

def windowKernelTimeMap (Phi : SpaceTime → ℝ) (hPhi : IsSmoothOnSpaceTime Phi)
    (z : SpaceTime) (a b : ℝ) (s : ℝ) : C(Torus3, ℝ) :=
  { toFun := fun x => Phi (z - (a + (b - a) * s, x))
    continuous_toFun := by
      exact (continuous_of_isSmoothOnSpaceTime hPhi).comp (by fun_prop) }

def windowKernelLift (Phi : SpaceTime → ℝ) (hPhi : IsSmoothOnSpaceTime Phi)
    (z : SpaceTime) (a b : ℝ)
    (_hends : windowKernelTimeMap Phi hPhi z a b 0 = windowKernelTimeMap Phi hPhi z a b 1) :
    UnitAddTorus (Fin 4) → ℝ :=
  fun y =>
    (AddCircle.liftIoc (1 : ℝ) 0 (windowKernelTimeMap Phi hPhi z a b) (y 0))
      (fun i : Fin 3 => y i.succ)

theorem continuous_windowKernelLift
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi) {z : SpaceTime} {a b : ℝ}
    (hends : windowKernelTimeMap Phi hPhi z a b 0 = windowKernelTimeMap Phi hPhi z a b 1)
    (hcont : ContinuousOn (windowKernelTimeMap Phi hPhi z a b) (Icc (0 : ℝ) 1)) :
    Continuous (windowKernelLift Phi hPhi z a b hends) := by
  let htime : Continuous (AddCircle.liftIoc (1 : ℝ) 0
      (windowKernelTimeMap Phi hPhi z a b)) :=
    AddCircle.liftIoc_zero_continuous (p := (1 : ℝ)) hends hcont
  let htime' : C(UnitAddCircle, C(Torus3, ℝ)) :=
    ⟨AddCircle.liftIoc (1 : ℝ) 0 (windowKernelTimeMap Phi hPhi z a b), htime⟩
  have hunc : Continuous (Function.uncurry fun t x => htime' t x) :=
    ContinuousMap.continuous_uncurry_of_continuous htime'
  have hcoord : Continuous (fun y : UnitAddTorus (Fin 4) =>
      (y 0, fun i : Fin 3 => y i.succ)) := by
    fun_prop
  exact hunc.comp hcoord

theorem windowKernelLift_coe_apply
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi) {z : SpaceTime} {a b : ℝ}
    (hends : windowKernelTimeMap Phi hPhi z a b 0 = windowKernelTimeMap Phi hPhi z a b 1)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : Torus3) :
    windowKernelLift Phi hPhi z a b hends (coordinateInsert 0 (t : UnitAddCircle) x) =
      Phi (z - (a + (b - a) * t, x)) := by
  have htime := AddCircle.liftIoc_zero_coe_apply (p := (1 : ℝ))
    (f := windowKernelTimeMap Phi hPhi z a b) ht
  unfold windowKernelLift
  rw [show (fun i : Fin 3 =>
      (coordinateInsert 0 (t : UnitAddCircle) x) i.succ) = x by
    funext i
    simp [coordinateInsert]]
  change AddCircle.liftIoc (1 : ℝ) 0 (windowKernelTimeMap Phi hPhi z a b)
    (t : UnitAddCircle) x = _
  rw [htime]
  rfl

theorem continuous_windowKernelLift_eq_windowPoint
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) :
    ∃ hends : windowKernelTimeMap Phi hPhi z a b 0 =
        windowKernelTimeMap Phi hPhi z a b 1,
      Continuous (fun y : UnitAddTorus (Fin 4) =>
        windowKernelLift Phi hPhi z a b hends y) ∧
      (∀ y, windowKernelLift Phi hPhi z a b hends y =
        Phi (z - windowPoint a b y)) := by
  have hleft : ∀ x : Torus3,
      Phi (z - (a + (b - a) * (0 : ℝ), x)) = 0 := by
    intro x
    apply hR
    change R < |z.1 - (a + (b - a) * (0 : ℝ))|
    simp only [mul_zero, add_zero]
    rw [ha]
    by_cases hR0 : 0 ≤ R
    · have hzlow : -N < z.1 := (abs_lt.mp hz).1
      have hpos : 0 < z.1 - (-N - R - 1) := by linarith
      rw [abs_of_pos hpos]
      linarith
    · exact lt_of_lt_of_le (lt_of_not_ge hR0) (abs_nonneg _)
  have hright : ∀ x : Torus3,
      Phi (z - (a + (b - a) * (1 : ℝ), x)) = 0 := by
    intro x
    apply hR
    change R < |z.1 - (a + (b - a) * (1 : ℝ))|
    simp only [mul_one]
    rw [hb]
    rw [show a + (N + R + 1 - a) = N + R + 1 by ring]
    by_cases hR0 : 0 ≤ R
    · have hzupper : z.1 < N := (abs_lt.mp hz).2
      have hneg : z.1 - (N + R + 1) < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    · exact lt_of_lt_of_le (lt_of_not_ge hR0) (abs_nonneg _)
  have hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1 := by
    apply ContinuousMap.ext
    intro x
    change Phi (z - (a + (b - a) * (0 : ℝ), x)) =
      Phi (z - (a + (b - a) * (1 : ℝ), x))
    rw [hleft x, hright x]
  have hcont : Continuous (windowKernelTimeMap Phi hPhi z a b) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × Torus3 =>
      Phi (z - (a + (b - a) * p.1, p.2)))
    exact (continuous_of_isSmoothOnSpaceTime hPhi).comp (by fun_prop)
  refine ⟨hends, continuous_windowKernelLift hPhi hends hcont.continuousOn, ?_⟩
  intro y
  let t : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ)
  let x : Torus3 := fun i => y i.succ
  have ht : t ∈ Ioc (0 : ℝ) 1 := by
    simpa [t] using (AddCircle.equivIoc (1 : ℝ) 0 (y 0)).property
  have hy : coordinateInsert 0 (t : UnitAddCircle) x = y := by
    ext i
    refine Fin.succAboveCases 0 ?_ (fun q => ?_) i
    · simp [coordinateInsert, t]
    · simp [coordinateInsert, x]
  have hpoint : windowPoint a b y = (a + (b - a) * t, x) := by
    unfold windowPoint
    simp [t, x]
  rw [hpoint, ← hy]
  exact windowKernelLift_coe_apply hPhi hends ht x

end RegularityStructures.Phi43

end
