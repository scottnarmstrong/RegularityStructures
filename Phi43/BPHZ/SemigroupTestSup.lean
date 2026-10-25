/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.SemigroupTestLattice
public import Phi43.BPHZ.SemigroupTestPeriodise
public import RegularityStructures.Analysis.Kernel.Moments

/-!
# Sup bound for the periodised semigroup kernel

For `t ∈ (0, 1]` and `lam = t^(1/4)`, the periodised kernel satisfies
`|q^♯_t(x, u)| ≤ B lam⁻⁵` with `B` independent of `t, x, u`
(`abs_semigroupPeriodised_le`).

* `abs_parabolicKernel_le_decay`: `|q_t(z)| ≤ C t^(-5/4) ∏ᵢ (1 + |zᵢ|)⁻²` for `t ≤ 1`, from the
  decay of `g_1, k_1` and exact parabolic scaling, using `lam ≤ 1` to compare the dilated and
  undilated spatial profiles.
* the lattice sum over `k ∈ ℤ³` is bounded uniformly by `exists_lattice_sum_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem rpow_quarter_pow_five_inv {t : ℝ} (ht : 0 < t) :
    (((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹) = t ^ (-(5 / 4 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
  norm_num

/-- The profile `(1 + |b|)^(-2)` in inverse-square form. -/
private theorem decay_two_eq (b : ℝ) :
    (1 + |b|) ^ (-((2 : ℕ) : ℝ)) = ((1 + |b|) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- Pointwise decay of the unit-scale parabolic kernel (time factor bounded, three quadratic
spatial profiles). -/
theorem exists_abs_parabolicKernel_one_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace,
      |parabolicKernel 1 z| ≤ C * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
  obtain ⟨Cg, hCg⟩ := heatKernel1D_one_decay 0
  obtain ⟨Ck, hCk⟩ := quarticKernel_one_decay 2
  have hCg0 : 0 ≤ Cg := by
    have := (abs_nonneg _).trans (hCg 0)
    simpa using this
  have hCk0 : 0 ≤ Ck := by
    have h := (abs_nonneg _).trans (hCk 0)
    simpa using h
  refine ⟨Cg * Ck ^ 3, by positivity, fun z => ?_⟩
  have hg : |heatKernel1D 1 z.1| ≤ Cg := by
    have := hCg z.1
    simpa using this
  have hk : ∀ i, |quarticKernel 1 (z.2 i)| ≤ Ck * ((1 + |z.2 i|) ^ 2)⁻¹ := by
    intro i
    have := hCk (z.2 i)
    rwa [decay_two_eq] at this
  unfold parabolicKernel
  rw [abs_mul, Finset.abs_prod]
  calc |heatKernel1D 1 z.1| * ∏ i, |quarticKernel 1 (z.2 i)|
      ≤ Cg * ∏ i : Fin 3, (Ck * ((1 + |z.2 i|) ^ 2)⁻¹) := by
        refine mul_le_mul hg (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hk i)
          (Finset.prod_nonneg fun i _ => abs_nonneg _) hCg0
    _ = Cg * Ck ^ 3 * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp [mul_assoc]

/-- Decay of the parabolic kernel at scales `t ≤ 1`. -/
theorem exists_abs_parabolicKernel_le_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ z : ParabolicSpace,
      |parabolicKernel t z| ≤ C * t ^ (-(5 / 4 : ℝ)) * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_one_le
  refine ⟨C, hC0, fun {t} ht ht1 z => ?_⟩
  have hc1 : 1 ≤ t ^ (-(1 / 4 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  rw [parabolicKernel_eq_scale ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  have h := hC (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z)
  have hprod : ∏ i : Fin 3, ((1 + |(parabolicDilate (t ^ (-(1 / 4 : ℝ))) z).2 i|) ^ 2)⁻¹ ≤
      ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have hab : |z.2 i| ≤ |(parabolicDilate (t ^ (-(1 / 4 : ℝ))) z).2 i| := by
      simp only [parabolicDilate, Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [abs_of_nonneg (by linarith : 0 ≤ t ^ (-(1 / 4 : ℝ)))]
      nlinarith [abs_nonneg (z.2 i)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  calc t ^ (-(5 / 4 : ℝ)) * |parabolicKernel 1 (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z)|
      ≤ t ^ (-(5 / 4 : ℝ)) * (C * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hprod hC0))
          (Real.rpow_nonneg ht.le _)
    _ = C * t ^ (-(5 / 4 : ℝ)) * ∏ i : Fin 3, ((1 + |z.2 i|) ^ 2)⁻¹ := by ring

/-- **Sup bound for the periodised semigroup kernel.**  There is `B ≥ 0` such that for
`t ∈ (0, 1]`, every `x` and `u`, `|q^♯_t(x, u)| ≤ B (t^(1/4))⁻⁵`. -/
theorem exists_abs_semigroupPeriodised_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x : ParabolicSpace) (u : SpaceTime),
      |semigroupPeriodised t x u| ≤ B * (((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_le_decay
  obtain ⟨L, hL0, hL⟩ := exists_lattice_sum_le
  refine ⟨C * L, mul_nonneg hC0 hL0, fun {t} ht ht1 x u => ?_⟩
  rw [rpow_quarter_pow_five_inv ht]
  set a : Fin 3 → ℝ := fun i => x.2 i - torusRep u.2 i with ha
  set P : (Fin 3 → ℤ) → ℝ := fun k => ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹ with hP
  have hterm : ∀ k : Fin 3 → ℤ,
      |parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun i => (k i : ℝ))| ≤
        C * t ^ (-(5 / 4 : ℝ)) * P (-k) := by
    intro k
    rw [parabolicSemigroup_kernel_eq]
    refine (hC ht ht1 _).trans (le_of_eq ?_)
    simp only [hP, ha, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show x.2 i - (torusRep u.2 i + (k i : ℝ)) = x.2 i - torusRep u.2 i + -(k i : ℝ) by ring]
  obtain ⟨hPs, hPL⟩ := hL a
  have hPs' : Summable (fun k => P (-k)) := ((Equiv.neg (Fin 3 → ℤ)).summable_iff (f := P)).2 hPs
  have hPt : ∑' k, P (-k) = ∑' k, P k := (Equiv.neg (Fin 3 → ℤ)).tsum_eq P
  have hsum : Summable (fun k : Fin 3 → ℤ =>
      |parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun i => (k i : ℝ))|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm (hPs'.mul_left _)
  unfold semigroupPeriodised
  calc |∑' k : Fin 3 → ℤ, parabolicSemigroup.kernel t x
          (u.1, torusRep u.2 + fun i => (k i : ℝ))|
      ≤ ∑' k : Fin 3 → ℤ, |parabolicSemigroup.kernel t x
          (u.1, torusRep u.2 + fun i => (k i : ℝ))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun k : Fin 3 → ℤ => parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun i => (k i : ℝ))) (by simpa using hsum)
    _ ≤ ∑' k : Fin 3 → ℤ, C * t ^ (-(5 / 4 : ℝ)) * P (-k) :=
        hsum.tsum_le_tsum hterm (hPs'.mul_left _)
    _ = C * t ^ (-(5 / 4 : ℝ)) * ∑' k : Fin 3 → ℤ, P k := by rw [tsum_mul_left, hPt]
    _ ≤ C * t ^ (-(5 / 4 : ℝ)) * L :=
        mul_le_mul_of_nonneg_left hPL (mul_nonneg hC0 (Real.rpow_nonneg ht.le _))
    _ = C * L * t ^ (-(5 / 4 : ℝ)) := by ring

end RegularityStructures

end
