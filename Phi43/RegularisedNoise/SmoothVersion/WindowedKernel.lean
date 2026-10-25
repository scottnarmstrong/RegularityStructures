/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowedModes
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Coordinates for the window torus

The Fourier series on a finite time window is most conveniently written on
`UnitAddTorus (Fin 4)`.  This file records the measurable coordinate map back to
`ℝ × T³` and the elementary relation between its characters and the window modes.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace RegularityStructures.Phi43

def windowPoint (a b : ℝ) (y : UnitAddTorus (Fin 4)) : SpaceTime :=
  (a + (b - a) * (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ),
    fun i : Fin 3 => y i.succ)

theorem windowPoint_time_mem_Ioc {a b : ℝ} (hab : a < b)
    (y : UnitAddTorus (Fin 4)) :
    (windowPoint a b y).1 ∈ Ioc a b := by
  unfold windowPoint
  have hy := (AddCircle.equivIoc (1 : ℝ) 0 (y 0)).property
  change a + (b - a) * (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ) ∈ Ioc a b
  constructor
  · have hnonneg : 0 ≤ b - a := le_of_lt (sub_pos.mpr hab)
    nlinarith [hy.1]
  · have hpos : 0 < b - a := sub_pos.mpr hab
    nlinarith [hy.2]

theorem windowPoint_mem_windowInterval {a b : ℝ} (hab : a < b)
    (y : UnitAddTorus (Fin 4)) :
    windowPoint a b y ∈ windowInterval a b := by
  exact ⟨windowPoint_time_mem_Ioc hab y, mem_univ _⟩

theorem windowFourierModeShift_windowPoint {a b : ℝ} (hab : a < b)
    (k : WindowFrequency) (y : UnitAddTorus (Fin 4)) :
    windowFourierModeShift a b k (windowPoint a b y) =
      UnitAddTorus.mFourier k y := by
  unfold windowFourierModeShift windowPoint UnitAddTorus.mFourier
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have harg : (b - a)⁻¹ *
      (a + (b - a) * (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ) - a) =
      (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ) := by
    calc
      _ = (b - a)⁻¹ * ((b - a) *
          (AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ)) := by
            congr 1
            ring
      _ = _ := by field_simp
  rw [harg]
  change fourier (k 0) ((AddCircle.equivIoc (1 : ℝ) 0 (y 0) : ℝ) : UnitAddCircle) *
      ∏ i : Fin 3, fourier (k i.succ) (y i.succ) = _
  simp only [ContinuousMap.coe_mk, Fin.prod_univ_succ]
  rw [AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := (0 : ℝ)) (y := y 0)]

end RegularityStructures.Phi43

end
