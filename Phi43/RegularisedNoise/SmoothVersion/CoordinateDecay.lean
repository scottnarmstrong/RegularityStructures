/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.CoordinateFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# One-coordinate Fourier coefficient reduction

This is the measure-theoretic reduction used in the finite-window decay estimate.  The first
coordinate of a multidimensional torus coefficient is a one-dimensional Fourier coefficient of a
coordinate slice, multiplied by the remaining characters.  The reduction keeps the slice
explicit, so the endpoint-vanishing integration-by-parts theorem can be applied without changing
the project convention for points of `T³`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators
open scoped ContDiff Topology

namespace RegularityStructures.Phi43

theorem integral_mFourier_coordinate_eq_const_mul_fourierCoeffOn
    {n : ℕ} (i : Fin (n + 1)) (f : UnitAddTorus (Fin (n + 1)) → ℂ)
    (k : Fin (n + 1) → ℤ) (x : UnitAddTorus (Fin n)) :
    (∫ t : UnitAddCircle,
        UnitAddTorus.mFourier (-k) (coordinateInsert i t x) •
          f (coordinateInsert i t x)) =
      (∏ j : Fin n, fourier (-(k (i.succAbove j))) (x j)) *
        fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
          (fun t : ℝ => f (coordinateInsert i (t : UnitAddCircle) x)) (k i) := by
  let c : ℂ := ∏ j : Fin n, fourier (-(k (i.succAbove j))) (x j)
  let s : UnitAddCircle → ℂ := fun t => f (coordinateInsert i t x)
  have hprod : ∀ t : UnitAddCircle,
      (∏ j : Fin (n + 1), fourier (-(k j)) (coordinateInsert i t x j)) =
        fourier (-(k i)) t * c := by
    intro t
    let p : Fin n → ℂ := fun j => fourier (-(k (i.succAbove j))) (x j)
    have hp : (fun j : Fin (n + 1) =>
        fourier (-(k j)) (coordinateInsert i t x j)) =
        Fin.insertNth i (fourier (-(k i)) t) p := by
      funext j
      refine Fin.succAboveCases i ?_ (fun q => ?_) j
      · simp [p, coordinateInsert]
      · simp [p, coordinateInsert]
    rw [show (∏ j : Fin (n + 1),
        fourier (-(k j)) (coordinateInsert i t x j)) =
        ∏ j, (Fin.insertNth i (fourier (-(k i)) t) p) j by rw [hp]]
    rw [Fin.prod_insertNth]
  have hrewrite : ∀ t : UnitAddCircle,
      UnitAddTorus.mFourier (-k) (coordinateInsert i t x) •
          f (coordinateInsert i t x) =
        c * (fourier (-(k i)) t * s t) := by
    intro t
    change (∏ j : Fin (n + 1),
        fourier ((-k) j) (coordinateInsert i t x j)) *
      f (coordinateInsert i t x) = _
    rw [show (fun j : Fin (n + 1) =>
        fourier ((-k) j) (coordinateInsert i t x j)) =
        (fun j : Fin (n + 1) => fourier (-(k j)) (coordinateInsert i t x j)) by
      funext j
      rw [Pi.neg_apply]]
    rw [hprod]
    ring
  have hinterval :
      (∫ t : UnitAddCircle, fourier (-(k i)) t * s t) =
        fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
          (fun t : ℝ => s (t : UnitAddCircle)) (k i) := by
    rw [fourierCoeffOn_eq_integral (fun t : ℝ => s (t : UnitAddCircle)) (k i)
      (show (0 : ℝ) < 1 by norm_num)]
    simp only [one_div, sub_zero, inv_one, one_smul, smul_eq_mul]
    rw [← UnitAddCircle.intervalIntegral_preimage (E := ℂ) 0
      (fun t : UnitAddCircle => fourier (-(k i)) t * s t)]
    rw [show (0 : ℝ) + 1 = 1 by norm_num]
    convert rfl using 1
    norm_num
  rw [integral_congr_ae (ae_of_all _ (fun t => hrewrite t))]
  rw [integral_const_mul]
  rw [hinterval]

theorem norm_mFourierCoeff_le_of_coordinate_decay_periodic
    {n : ℕ} (i : Fin (n + 1)) (f : UnitAddTorus (Fin (n + 1)) → ℂ)
    (k : Fin (n + 1) → ℤ) (hf : Continuous f) {m : ℕ} (hki : k i ≠ 0)
    (hslice : ∀ x : UnitAddTorus (Fin n),
      ContDiff ℝ ∞ (fun t : ℝ => f (coordinateInsert i (t : UnitAddCircle) x)))
    (hperiod : ∀ x : UnitAddTorus (Fin n), ∀ j < m,
      iteratedDeriv j (fun t : ℝ => f (coordinateInsert i (t : UnitAddCircle) x)) 1 =
        iteratedDeriv j (fun t : ℝ => f (coordinateInsert i (t : UnitAddCircle) x)) 0)
    {C : ℝ}
    (hbound : ∀ x : UnitAddTorus (Fin n),
      ((1 : ℝ) / (2 * Real.pi * |(k i : ℝ)|)) ^ m *
          ((1 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
            ‖iteratedDeriv m
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) t‖) ≤ C) :
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤ C := by
  rw [mFourierCoeff_eq_coordinateIntegral i f k hf]
  calc
    ‖∫ x : UnitAddTorus (Fin n),
        (∫ t : UnitAddCircle,
          UnitAddTorus.mFourier (-k) (coordinateInsert i t x) •
            f (coordinateInsert i t x))‖ ≤
        C * (volume : Measure (UnitAddTorus (Fin n))).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with x
      have hderiv : ∀ j < m, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          HasDerivAt
            (iteratedDeriv j
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)))
            (iteratedDeriv (j + 1)
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) t) t := by
        intro j hj t ht
        have hjtop : (j : ℕ∞ω) < (∞ : ℕ∞ω) :=
          WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
        have hdiff : DifferentiableAt ℝ
            (iteratedDeriv j
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x))) t :=
          ((hslice x).differentiable_iteratedDeriv j hjtop).differentiableAt
        simpa [iteratedDeriv_succ] using hdiff.hasDerivAt
      have hperiod' : ∀ j < m,
          iteratedDeriv j
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) 1 =
            iteratedDeriv j
              (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) 0 := by
        intro j hj
        exact hperiod x j hj
      have hinterval : ∀ j, IntervalIntegrable
          (iteratedDeriv j
            (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x))) volume 0 1 := by
        intro j
        have hjtop : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
          WithTop.coe_le_coe.mpr le_top
        exact ((hslice x).continuous_iteratedDeriv j hjtop).continuousOn.intervalIntegrable
      have hcoeff := norm_fourierCoeffOn_le_of_derivative_chain
        (show (0 : ℝ) < 1 by norm_num) hki hderiv hperiod' hinterval
      have hinner := integral_mFourier_coordinate_eq_const_mul_fourierCoeffOn i f k x
      rw [hinner]
      have hc : ‖∏ j : Fin n, fourier (-(k (i.succAbove j))) (x j)‖ = 1 := by
        simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
      rw [norm_mul, hc, one_mul]
      calc
        ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
            (fun t : ℝ => f (coordinateInsert i (t : UnitAddCircle) x)) (k i)‖ ≤
            ((1 - 0) / (2 * Real.pi * |(k i : ℝ)|)) ^ m *
              ((1 - 0)⁻¹ * ∫ t in (0 : ℝ)..1,
                ‖iteratedDeriv m
                  (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) t‖) := hcoeff
        _ = ((1 : ℝ) / (2 * Real.pi * |(k i : ℝ)|)) ^ m *
              ((1 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
                ‖iteratedDeriv m
                  (fun s : ℝ => f (coordinateInsert i (s : UnitAddCircle) x)) t‖) := by
          norm_num
        _ ≤ C := hbound x
    _ = C := by
      have hvol : (volume : Measure (UnitAddTorus (Fin n))).real Set.univ = 1 := by
        change (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))).real Set.univ = 1
        rw [Measure.real, Measure.pi_univ]
        simp
      rw [hvol, mul_one]

end RegularityStructures.Phi43

end
