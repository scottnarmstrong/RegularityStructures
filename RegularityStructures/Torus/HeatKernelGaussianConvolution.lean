/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.Probability.SpaceTimeMeasure
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Euclidean Gaussian convolution

This is the Euclidean calculation behind the semigroup identity for the periodised heat kernel.
The statement is kept on `Fin 3 → ℝ`, matching the torus implementation and avoiding an
`EuclideanSpace` coercion at the stochastic interface.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures

private theorem sqNorm3_sub_smul_add (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y : Fin 3 → ℝ) :
    sqNorm3 y / s + sqNorm3 (x - y) / t =
      sqNorm3 x / (s + t) +
        sqNorm3 (y - (s / (s + t)) • x) / (s * t / (s + t)) := by
  have hst : 0 < s + t := by linarith
  have hst0 : s + t ≠ 0 := ne_of_gt hst
  have hq0 : s * t / (s + t) ≠ 0 := ne_of_gt (div_pos (mul_pos hs ht) hst)
  unfold sqNorm3
  rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, Finset.sum_div]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp
  field_simp [hst0, hq0]
  ring

private theorem gaussKernel_mul_gaussKernel_sub_eq (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y : Fin 3 → ℝ) :
    gaussKernel s y * gaussKernel t (x - y) =
      gaussKernel (s + t) x * gaussKernel (s * t / (s + t))
        (y - (s / (s + t)) • x) := by
  have hst : 0 < s + t := by linarith
  have hq : 0 < s * t / (s + t) := div_pos (mul_pos hs ht) hst
  have h4s : 0 < 4 * π * s := by positivity
  have h4t : 0 < 4 * π * t := by positivity
  have h4st : 0 < 4 * π * (s + t) := by positivity
  have h4q : 0 < 4 * π * (s * t / (s + t)) := by positivity
  rw [gaussKernel, gaussKernel, gaussKernel, gaussKernel]
  have hquad : sqNorm3 y / (4 * s) + sqNorm3 (x - y) / (4 * t) =
      sqNorm3 x / (4 * (s + t)) +
        sqNorm3 (y - (s / (s + t)) • x) / (4 * (s * t / (s + t))) := by
    calc
      _ = (sqNorm3 y / s + sqNorm3 (x - y) / t) / 4 := by ring
      _ = (sqNorm3 x / (s + t) +
          sqNorm3 (y - (s / (s + t)) • x) / (s * t / (s + t))) / 4 := by
        rw [sqNorm3_sub_smul_add s t hs ht x y]
      _ = _ := by
        field_simp [ne_of_gt hs, ne_of_gt ht, ne_of_gt hst]
  have hconst : (4 * π * s) ^ (-(3 : ℝ) / 2) *
      (4 * π * t) ^ (-(3 : ℝ) / 2) =
      (4 * π * (s + t)) ^ (-(3 : ℝ) / 2) *
        (4 * π * (s * t / (s + t))) ^ (-(3 : ℝ) / 2) := by
    have he : (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) := by ring
    rw [he]
    rw [Real.rpow_neg h4s.le, Real.rpow_neg h4t.le,
      Real.rpow_neg h4st.le, Real.rpow_neg h4q.le]
    rw [← mul_inv, ← mul_inv]
    rw [← Real.mul_rpow h4s.le h4t.le, ← Real.mul_rpow h4st.le h4q.le]
    have hprod : (4 * π * s) * (4 * π * t) =
        (4 * π * (s + t)) * (4 * π * (s * t / (s + t))) := by
      field_simp [ne_of_gt hst]
    rw [hprod]
  calc
    _ = ((4 * π * s) ^ (-(3 : ℝ) / 2) *
          (4 * π * t) ^ (-(3 : ℝ) / 2)) *
        (exp (-sqNorm3 y / (4 * s)) *
          exp (-sqNorm3 (x - y) / (4 * t))) := by ring
    _ = ((4 * π * s) ^ (-(3 : ℝ) / 2) *
          (4 * π * t) ^ (-(3 : ℝ) / 2)) *
        exp (-sqNorm3 y / (4 * s) - sqNorm3 (x - y) / (4 * t)) := by
          rw [← exp_add]
          congr 1; ring_nf
    _ = ((4 * π * (s + t)) ^ (-(3 : ℝ) / 2) *
          (4 * π * (s * t / (s + t))) ^ (-(3 : ℝ) / 2)) *
        exp (-sqNorm3 x / (4 * (s + t)) -
          sqNorm3 (y - (s / (s + t)) • x) /
            (4 * (s * t / (s + t)))) := by
          rw [hconst]
          have hexp : exp (-sqNorm3 y / (4 * s) - sqNorm3 (x - y) / (4 * t)) =
              exp (-sqNorm3 x / (4 * (s + t)) -
                sqNorm3 (y - (s / (s + t)) • x) /
                  (4 * (s * t / (s + t)))) := by
            congr 1
            rw [show -sqNorm3 y / (4 * s) - sqNorm3 (x - y) / (4 * t) =
                -(sqNorm3 y / (4 * s) + sqNorm3 (x - y) / (4 * t)) by ring,
              hquad]
            ring
          rw [hexp]
    _ = _ := by
          rw [show (4 * π * (s + t)) ^ (-(3 : ℝ) / 2) *
              (4 * π * (s * t / (s + t))) ^ (-(3 : ℝ) / 2) *
              exp (-sqNorm3 x / (4 * (s + t)) -
                sqNorm3 (y - (s / (s + t)) • x) /
                  (4 * (s * t / (s + t)))) =
              ((4 * π * (s + t)) ^ (-(3 : ℝ) / 2) *
                (4 * π * (s * t / (s + t))) ^ (-(3 : ℝ) / 2)) *
                (exp (-sqNorm3 x / (4 * (s + t))) *
                  exp (-sqNorm3 (y - (s / (s + t)) • x) /
                    (4 * (s * t / (s + t))))) by
                rw [← exp_add]
                congr 1; ring_nf]
          ring

theorem integral_gaussKernel_mul_gaussKernel_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : Fin 3 → ℝ) :
    ∫ y : Fin 3 → ℝ, gaussKernel s y * gaussKernel t (x - y) =
      gaussKernel (s + t) x := by
  let q : ℝ := s * t / (s + t)
  let a : Fin 3 → ℝ := (s / (s + t)) • x
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos hs ht) (by linarith)
  have hshift : Integrable (fun y : Fin 3 → ℝ => gaussKernel q (y - a)) := by
    have h := integrable_gaussKernel hq
    have hp := measurePreserving_add_left (volume : Measure (Fin 3 → ℝ)) (-a)
    have hp' := hp.integrable_comp_of_integrable h
    convert hp' using 1
    funext y
    congr 1
    exact sub_eq_neg_add y a
  have hrewrite : (fun y : Fin 3 → ℝ => gaussKernel s y * gaussKernel t (x - y)) =
      (fun y => gaussKernel (s + t) x * gaussKernel q (y - a)) := by
    funext y
    dsimp [q, a]
    exact gaussKernel_mul_gaussKernel_sub_eq s t hs ht x y
  rw [hrewrite, integral_const_mul]
  have htrans : ∫ y : Fin 3 → ℝ, gaussKernel q (y - a) =
      ∫ y : Fin 3 → ℝ, gaussKernel q y := by
    have h := integral_add_left_eq_self
      (μ := (volume : Measure (Fin 3 → ℝ)))
      (fun y : Fin 3 → ℝ => gaussKernel q y) (-a)
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1
    abel
  rw [htrans]
  rw [integral_gaussKernel hq]
  simp

end RegularityStructures

end
