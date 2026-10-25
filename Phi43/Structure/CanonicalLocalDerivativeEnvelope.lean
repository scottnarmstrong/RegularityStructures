/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalDerivativeGrowthAlgebra
import RegularityStructures.Analysis.Kernel.GeneratorLip
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative local increments from polynomial derivative growth

An ingredient of Hairer [Hai14, Proposition 8.27] in the polynomially
weighted framework [Hos25, Definition 2.1]. The local Lipschitz constant
has an explicit polynomial envelope in its base point.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem norm_small {v : ParabolicSpace} (hv : parabolicNorm v ≤ 1) :
    ‖v‖ ≤ parabolicNorm v := by
  have hs : Real.sqrt |v.1| ≤ parabolicNorm v := by
    unfold parabolicNorm
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have ht : |v.1| ≤ 1 := by
    nlinarith [Real.sq_sqrt (abs_nonneg v.1), Real.sqrt_nonneg |v.1|]
  exact RegularityStructures.norm_le_parabolicNorm ht

private theorem parabolicNorm_of_norm_small {v : ParabolicSpace} (hv : ‖v‖ ≤ 1) :
    parabolicNorm v ≤ 4 := by
  have ht : |v.1| ≤ 1 := by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv
  have hs : Real.sqrt |v.1| ≤ 1 := (Real.sqrt_le_one).2 ht
  have hx (i : Fin 3) : |v.2 i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using ((norm_le_pi_norm v.2 i).trans (norm_snd_le v)).trans hv
  have hsum : (∑ i : Fin 3, |v.2 i|) ≤ 3 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin 3 => (1 : ℝ))
      (fun i _ => hx i)
  unfold parabolicNorm
  linarith

open scoped ContDiff in
/-- The polynomial envelope of the derivative yields an explicit local
increment envelope, uniformly in the base point. -/
theorem canonicalSmooth_local_increment_of_derivative_bound
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (C : ℝ) (p : ℕ)
    (hder : ∀ z, ‖fderiv ℝ f z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (x y : ParabolicSpace) (hxy : parabolicNorm (y - x) ≤ 1) :
    |f y - f x| ≤ C * 5 ^ p * (1 + parabolicNorm x) ^ p * parabolicNorm (y - x) := by
  have hC : 0 ≤ C := by
    have hh := (norm_nonneg (fderiv ℝ f 0)).trans (hder 0)
    simpa only [parabolicNorm_zero, add_zero, one_pow, mul_one] using hh
  have hn := norm_small hxy
  have hbound (z : ParabolicSpace) (hz : z ∈ Metric.closedBall x 1) :
      ‖fderiv ℝ f z‖ ≤ C * 5 ^ p * (1 + parabolicNorm x) ^ p := by
    have hzn : ‖z - x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzpar := parabolicNorm_of_norm_small hzn
    have hh := parabolicNorm_add_le (z - x) x
    rw [sub_add_cancel] at hh
    have hbase : 1 + parabolicNorm z ≤ 5 * (1 + parabolicNorm x) := by
      linarith [parabolicNorm_nonneg x]
    have hpow := pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg z]) hbase p
    rw [mul_pow] at hpow
    exact (hder z).trans ((mul_le_mul_of_nonneg_left hpow hC).trans_eq (by ring))
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Metric.closedBall x 1) => hf.differentiable (by simp) z)
    hbound (convex_closedBall x 1) (Metric.mem_closedBall_self (by norm_num))
    (show y ∈ Metric.closedBall x 1 by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hn.trans hxy)
  have hc0 : 0 ≤ C * 5 ^ p * (1 + parabolicNorm x) ^ p :=
    mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (by linarith [parabolicNorm_nonneg x]) p)
  have hm' : |f y - f x| ≤ C * 5 ^ p * (1 + parabolicNorm x) ^ p * ‖y - x‖ := by
    simpa only [Real.norm_eq_abs] using hm
  exact hm'.trans (mul_le_mul_of_nonneg_left hn hc0)

end RegularityStructures.Phi43

end
