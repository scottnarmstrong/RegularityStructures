/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowedModes
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Character identities for translated finite-window kernels

The finite-window Fourier modes are restrictions of group characters.  This file records the
translation identity in the form used to separate the frequency coefficient from the space-time
character in a white-noise series.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace RegularityStructures.Phi43

def globalWindowFourierMode (L : ℝ) (k : Fin 4 → ℤ) (z : SpaceTime) : ℂ :=
  fourier (k 0) ((L⁻¹ * z.1 : ℝ) : UnitAddCircle) *
    ∏ i : Fin 3, fourier (k i.succ) (z.2 i)

private theorem fourier_sub (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  rw [fourier_apply, fourier_apply, fourier_apply, sub_eq_add_neg, zsmul_add,
    AddCircle.toCircle_add, zsmul_neg, AddCircle.toCircle_neg,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

theorem globalWindowFourierMode_sub {L : ℝ}
    (k : Fin 4 → ℤ) (z w : SpaceTime) :
    globalWindowFourierMode L k (z - w) =
      globalWindowFourierMode L k z * conj (globalWindowFourierMode L k w) := by
  unfold globalWindowFourierMode
  have htime :
      fourier (k 0) ((L⁻¹ * (z.1 - w.1) : ℝ) : UnitAddCircle) =
        fourier (k 0) ((L⁻¹ * z.1 : ℝ) : UnitAddCircle) *
          conj (fourier (k 0) ((L⁻¹ * w.1 : ℝ) : UnitAddCircle)) := by
    rw [show L⁻¹ * (z.1 - w.1) = L⁻¹ * z.1 - L⁻¹ * w.1 by ring]
    simpa using
      (fourier_sub (k 0) ((L⁻¹ * z.1 : ℝ) : UnitAddCircle)
        ((L⁻¹ * w.1 : ℝ) : UnitAddCircle))
  change fourier (k 0) ((L⁻¹ * (z.1 - w.1) : ℝ) : UnitAddCircle) *
      (∏ i : Fin 3, fourier (k i.succ) (z.2 i - w.2 i)) = _
  rw [htime]
  have hsp : ∀ i : Fin 3,
      fourier (k i.succ) (z.2 i - w.2 i) =
        fourier (k i.succ) (z.2 i) * conj (fourier (k i.succ) (w.2 i)) := by
    intro i
    exact fourier_sub _ _ _
  simp_rw [hsp]
  rw [Finset.prod_mul_distrib]
  simp only [map_mul, map_prod]
  ring

theorem windowFourierModeShift_eq_globalWindowFourierMode_mul
    {a b : ℝ} (hab : a < b) (k : WindowFrequency) (z : SpaceTime) :
    windowFourierModeShift a b k z =
      globalWindowFourierMode (b - a) k z *
        conj (globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0)) := by
  unfold windowFourierModeShift globalWindowFourierMode
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have htime :
      ((b - a)⁻¹ * (z.1 - a) : ℝ) =
        (b - a)⁻¹ * z.1 - (b - a)⁻¹ * a := by ring
  rw [htime]
  change fourier (k 0)
      (((b - a)⁻¹ * z.1 - (b - a)⁻¹ * a : ℝ) : UnitAddCircle) *
      (∏ i : Fin 3, fourier (k i.succ) (z.2 i)) = _
  rw [show (((b - a)⁻¹ * z.1 - (b - a)⁻¹ * a : ℝ) : UnitAddCircle) =
      ((b - a)⁻¹ * z.1 : ℝ) - ((b - a)⁻¹ * a : ℝ) by
        rw [AddCircle.coe_sub], fourier_sub]
  simp only [map_mul, map_prod]
  simp
  ring

end RegularityStructures.Phi43

end
