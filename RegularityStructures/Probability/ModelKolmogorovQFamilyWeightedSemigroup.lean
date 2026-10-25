/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Weighted.Operator

/-!
# Polynomial weights for the parabolic Q-semigroup

The global annealed hypothesis uses the Hoshino-type weight
`ρ_q(y) = (1 + ‖y‖_𝔰)^q`.  This module proves that this weight is moderate for the auxiliary
parabolic semigroup.  Consequently the weighted operator estimates apply without adding a
localization or compact-support hypothesis to the stochastic input.

The weight convention follows [Hos25, Definitions 2.1 and 2.6] (arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

def parabolicPolynomialWeight (q : ℝ) (z : ParabolicSpace) : ℝ :=
  (1 + parabolicNorm z) ^ q

theorem parabolicPolynomialWeight_one_le {q : ℝ} (hq : 0 ≤ q) (z : ParabolicSpace) :
    1 ≤ parabolicPolynomialWeight q z := by
  unfold parabolicPolynomialWeight
  exact Real.one_le_rpow (by linarith [parabolicNorm_nonneg z]) hq

theorem measurable_parabolicPolynomialWeight {q : ℝ} (hq : 0 ≤ q) :
    Measurable (parabolicPolynomialWeight q) := by
  have hbase : Continuous (fun z : ParabolicSpace => 1 + parabolicNorm z) :=
    continuous_const.add continuous_parabolicNorm
  change Measurable (fun z : ParabolicSpace => (1 + parabolicNorm z) ^ q)
  exact (Real.continuous_rpow_const hq).comp hbase |>.measurable

theorem parabolicPolynomialWeight_le_mul {q : ℝ} (hq : 0 ≤ q)
    (y z : ParabolicSpace) :
    parabolicPolynomialWeight q z ≤ parabolicPolynomialWeight q y *
      (1 + parabolicNorm (z - y)) ^ q := by
  unfold parabolicPolynomialWeight
  have hnorm : parabolicNorm z ≤ parabolicNorm y + parabolicNorm (z - y) := by
    calc
      parabolicNorm z = parabolicNorm (y + (z - y)) := by ring_nf
      _ ≤ parabolicNorm y + parabolicNorm (z - y) := parabolicNorm_add_le _ _
  have hbase : 1 + parabolicNorm z ≤
      (1 + parabolicNorm y) * (1 + parabolicNorm (z - y)) := by
    have hy := parabolicNorm_nonneg y
    have hz := parabolicNorm_nonneg (z - y)
    nlinarith
  calc
    (1 + parabolicNorm z) ^ q ≤
        ((1 + parabolicNorm y) * (1 + parabolicNorm (z - y))) ^ q :=
      Real.rpow_le_rpow (add_nonneg zero_le_one (parabolicNorm_nonneg z)) hbase hq
    _ = (1 + parabolicNorm y) ^ q * (1 + parabolicNorm (z - y)) ^ q := by
      rw [Real.mul_rpow (add_nonneg zero_le_one (parabolicNorm_nonneg y))
        (add_nonneg zero_le_one (parabolicNorm_nonneg (z - y)))]

theorem isModerateWeight_parabolicPolynomial {q : ℝ} (hq : 0 ≤ q) :
    parabolicSemigroup.IsModerateWeight (parabolicPolynomialWeight q) q where
  one_le := parabolicPolynomialWeight_one_le hq
  measurable := measurable_parabolicPolynomialWeight hq
  nonneg_exp := hq
  le := parabolicPolynomialWeight_le_mul hq

end RegularityStructures

end
