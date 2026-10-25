/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestSup

/-!
# Polynomially weighted decay of the semigroup kernel

For `t ∈ (0, 1]` and `lam = t^(1/4)`, the kernel satisfies, for every `β ∈ ℕ`,
`|q_t(z)| (‖z‖_𝔰 / lam)^β ≤ C t^(-5/4) ∏ᵢ (1 + |zᵢ|)⁻²` (`abs_parabolicKernel_mul_norm_le`).
The proof uses `‖z‖_𝔰 ≤ (1 + |z₀|) ∏ᵢ (1 + |zᵢ|)` and the decay of the one-dimensional kernels of
every order, then exact parabolic scaling.
-/

public section

namespace RegularityStructures

theorem parabolicNorm_le_prod (z : ParabolicSpace) :
    parabolicNorm z ≤ (1 + |z.1|) * ∏ i : Fin 3, (1 + |z.2 i|) := by
  unfold parabolicNorm
  simp only [Fin.prod_univ_three, Fin.sum_univ_three]
  have h1 : Real.sqrt |z.1| ≤ 1 + |z.1| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg z.1]
  nlinarith [abs_nonneg z.1, abs_nonneg (z.2 0), abs_nonneg (z.2 1), abs_nonneg (z.2 2),
    mul_nonneg (abs_nonneg (z.2 0)) (abs_nonneg (z.2 1)),
    mul_nonneg (abs_nonneg (z.2 0)) (abs_nonneg (z.2 2)),
    mul_nonneg (abs_nonneg (z.2 1)) (abs_nonneg (z.2 2)),
    mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 0)),
    mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 1)),
    mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 2)),
    mul_nonneg (mul_nonneg (abs_nonneg (z.2 0)) (abs_nonneg (z.2 1))) (abs_nonneg (z.2 2)),
    mul_nonneg (mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 0))) (abs_nonneg (z.2 1)),
    mul_nonneg (mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 0))) (abs_nonneg (z.2 2)),
    mul_nonneg (mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 1))) (abs_nonneg (z.2 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg z.1) (abs_nonneg (z.2 0)))
      (abs_nonneg (z.2 1))) (abs_nonneg (z.2 2))]

private theorem rpow_neg_nat_mul_pow {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    a ^ (-((n : ℕ) : ℝ)) * a ^ m = a ^ ((m : ℤ) - n) := by
  rw [Real.rpow_neg ha.le, Real.rpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg,
    ← zpow_add₀ ha.ne']
  congr 1
  ring

/-- Unit-scale weighted decay of the parabolic kernel. -/
theorem exists_abs_parabolicKernel_one_mul_norm_le (β : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace,
      |parabolicKernel 1 z| * parabolicNorm z ^ β ≤ C * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
  obtain ⟨Cg, hCg⟩ := heatKernel1D_one_decay β
  obtain ⟨Ck, hCk⟩ := quarticKernel_one_decay (β + 2)
  have hCg0 : 0 ≤ Cg := by
    have := (abs_nonneg _).trans (hCg 0)
    simpa using this
  have hCk0 : 0 ≤ Ck := by
    have h := (abs_nonneg _).trans (hCk 0)
    simpa using h
  refine ⟨Cg * Ck ^ 3, by positivity, fun z => ?_⟩
  have hpos : ∀ b : ℝ, 0 < 1 + |b| := fun b => by positivity
  have hn : parabolicNorm z ^ β ≤ ((1 + |z.1|) ^ β) * ∏ i : Fin 3, (1 + |z.2 i|) ^ β := by
    calc parabolicNorm z ^ β ≤ ((1 + |z.1|) * ∏ i : Fin 3, (1 + |z.2 i|)) ^ β :=
          pow_le_pow_left₀ (by unfold parabolicNorm; positivity) (parabolicNorm_le_prod z) β
      _ = _ := by rw [mul_pow, Finset.prod_pow]
  have hg : |heatKernel1D 1 z.1| * (1 + |z.1|) ^ β ≤ Cg := by
    have h := mul_le_mul_of_nonneg_right (hCg z.1) (pow_nonneg (hpos z.1).le β)
    rw [mul_assoc, rpow_neg_nat_mul_pow (hpos z.1) β β] at h
    simpa using h
  have hk : ∀ i : Fin 3, |quarticKernel 1 (z.2 i)| * (1 + |z.2 i|) ^ β ≤
      Ck * ((1 + |z.2 i|) ^ 2)⁻¹ := by
    intro i
    have h := mul_le_mul_of_nonneg_right (hCk (z.2 i)) (pow_nonneg (hpos (z.2 i)).le β)
    rw [mul_assoc, rpow_neg_nat_mul_pow (hpos (z.2 i)) (β + 2) β] at h
    have e : (1 + |z.2 i|) ^ (((β : ℤ)) - ((β + 2 : ℕ) : ℤ)) = ((1 + |z.2 i|) ^ 2)⁻¹ := by
      rw [show ((β : ℤ)) - ((β + 2 : ℕ) : ℤ) = -((2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    rwa [e] at h
  unfold parabolicKernel
  rw [abs_mul, Finset.abs_prod]
  calc |heatKernel1D 1 z.1| * (∏ i : Fin 3, |quarticKernel 1 (z.2 i)|) * parabolicNorm z ^ β
      ≤ |heatKernel1D 1 z.1| * (∏ i : Fin 3, |quarticKernel 1 (z.2 i)|) *
        ((1 + |z.1|) ^ β * ∏ i : Fin 3, (1 + |z.2 i|) ^ β) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (|heatKernel1D 1 z.1| * (1 + |z.1|) ^ β) *
        ∏ i : Fin 3, (|quarticKernel 1 (z.2 i)| * (1 + |z.2 i|) ^ β) := by
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ Cg * ∏ i : Fin 3, (Ck * ((1 + |z.2 i|) ^ 2)⁻¹) := by
        refine mul_le_mul hg (Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hk i)
          (Finset.prod_nonneg fun i _ => by positivity) hCg0
    _ = Cg * Ck ^ 3 * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp [mul_assoc]

theorem parabolicNorm_dilate {c : ℝ} (hc : 0 ≤ c) (z : ParabolicSpace) :
    parabolicNorm (parabolicDilate c z) = c * parabolicNorm z := by
  unfold parabolicNorm parabolicDilate
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg
    (sq_nonneg c)]
  rw [mul_add, Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

/-- Weighted decay of the parabolic kernel at scales `t ≤ 1`. -/
theorem exists_abs_parabolicKernel_mul_norm_le (β : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ z : ParabolicSpace,
      |parabolicKernel t z| * (parabolicNorm z / t ^ (1 / 4 : ℝ)) ^ β ≤
        C * t ^ (-(5 / 4 : ℝ)) * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_one_mul_norm_le β
  refine ⟨C, hC0, fun {t} ht ht1 z => ?_⟩
  have hl : 0 < t ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos ht _
  have hc1 : 1 ≤ t ^ (-(1 / 4 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  have hdiv : parabolicNorm z / t ^ (1 / 4 : ℝ) = parabolicNorm (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z) := by
    rw [parabolicNorm_dilate hl.le, Real.rpow_neg ht.le, div_eq_inv_mul]
  rw [hdiv, parabolicKernel_eq_scale ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  have h := hC (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z)
  have hprod : ∏ i : Fin 3, ((1 + |(parabolicDilate (t ^ (-(1 / 4 : ℝ))) z).2 i|) ^ 2)⁻¹ ≤
      ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have hab : |z.2 i| ≤ |(parabolicDilate (t ^ (-(1 / 4 : ℝ))) z).2 i| := by
      simp only [parabolicDilate, Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [abs_of_nonneg (by linarith : 0 ≤ t ^ (-(1 / 4 : ℝ)))]
      nlinarith [abs_nonneg (z.2 i)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  calc t ^ (-(5 / 4 : ℝ)) * |parabolicKernel 1 (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z)| *
        parabolicNorm (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z) ^ β
      = t ^ (-(5 / 4 : ℝ)) * (|parabolicKernel 1 (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z)| *
        parabolicNorm (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z) ^ β) := by ring
    _ ≤ t ^ (-(5 / 4 : ℝ)) * (C * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hprod hC0))
          (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

end RegularityStructures

end
