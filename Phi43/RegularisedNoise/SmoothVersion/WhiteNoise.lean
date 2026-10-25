/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianVector
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# The L² isometry of an arbitrary white noise

The strengthened white-noise predicate supplies measurable Gaussian coordinates for every
square-integrable kernel.  The finite-dimensional covariance clause then gives the exact L²
isometry and the almost-sure identification of evaluations of equal kernels.  These are the
probabilistic identities used when a smooth Fourier series is compared with the original field.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

theorem whiteNoise_integral_sub_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    ∫ ω, (W h ω - W g ω) ^ (2 : ℕ) ∂P = ∫ z, (h z - g z) ^ (2 : ℕ) := by
  let f : Fin 2 → SpaceTime → ℝ := fun i => if i = 0 then h else g
  let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  have hf : ∀ i, MemLp (f i) 2 (volume : Measure SpaceTime) := by
    intro i
    fin_cases i <;> simp [f, hh, hg]
  have hcent := hW.2 2 f hf
  have hlin := hcent.integral_linear_sq (σ := id) a
  have hright :
      (∑ m, ∑ m', a m * a m' * ∫ z, f m z * f m' z) =
        ∫ z, (h z - g z) ^ (2 : ℕ) := by
    have hrhs :
        (∫ z, (h z - g z) ^ (2 : ℕ)) =
          ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
      calc
        (∫ z, (h z - g z) ^ (2 : ℕ)) =
            ∫ z, h z * h z - h z * g z - g z * h z + g z * g z := by
              congr 1
              funext z
              ring
        _ = ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
              have hhh := hh.integrable_mul hh
              have hhg := hh.integrable_mul hg
              have hgh := hg.integrable_mul hh
              have hgg := hg.integrable_mul hg
              change (∫ z, ((h * h - h * g - g * h) z + (g * g) z)) = _
              rw [integral_add ((hhh.sub hhg).sub hgh) hgg]
              change (∫ z, ((h * h - h * g) z - (g * h) z)) + _ = _
              rw [integral_sub (hhh.sub hhg) hgh]
              change ((∫ z, ((h * h) z - (h * g) z)) - _) + _ = _
              rw [integral_sub hhh hhg]
              simp only [Pi.mul_apply]
    calc
      (∑ m, ∑ m', a m * a m' * ∫ z, f m z * f m' z) =
          ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
              simp [f, a, Fin.sum_univ_two]
              ring
      _ = ∫ z, (h z - g z) ^ (2 : ℕ) := hrhs.symm
  rw [← hright]
  convert hlin using 1
  · simp [f, a, Fin.sum_univ_two, sub_eq_add_neg]
  · exact rfl

end RegularityStructures.Phi43

end
