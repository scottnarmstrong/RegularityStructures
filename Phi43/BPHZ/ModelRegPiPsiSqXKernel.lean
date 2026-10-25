/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestSup
public import Phi43.BPHZ.ModelRegPiXiTranslate

/-!
# The coordinate-weighted periodised semigroup kernel

For `i : Fin 3` the *coordinate-weighted periodised kernel* is
`g_i(u) = ∑_{k ∈ ℤ³} Q_t(x, (u₀, torusRep u' + k)) ((torusRep u' + k)ᵢ - xᵢ)`
(`semigroupPeriodisedX`), the periodisation of `y ↦ Q_t(x, y) (yᵢ - xᵢ)` on `ℝ⁴`.  It is the test
function against which the field `:Ψ²:` is integrated in the realisation of the tree `Ψ² Xᵢ`.

This file proves the sup bound `|g_i(u)| ≤ B lam (lam⁵)⁻¹` for `t ∈ (0, 1]`, `lam = t^(1/4)`
(`exists_abs_semigroupPeriodisedX_le`): the extra factor `|zᵢ|` of the displacement is absorbed by
the cubic decay of the quartic kernel, and gains a factor `lam` by parabolic scaling.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The coordinate-weighted periodised semigroup kernel (the periodisation of
`Q_t(x, y) (yᵢ - xᵢ)`). -/
def semigroupPeriodisedX (t : ℝ) (x : ParabolicSpace) (i : Fin 3) (u : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ)) *
    ((torusRep u.2 i + (k i : ℝ)) - x.2 i)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

private theorem decay_three_eq (b : ℝ) :
    (1 + |b|) ^ (-((3 : ℕ) : ℝ)) = ((1 + |b|) ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

private theorem cube_aux (u v w : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    (u ^ 3)⁻¹ * (v ^ 3)⁻¹ * (w ^ 3)⁻¹ * u ≤ (u ^ 2)⁻¹ * (v ^ 2)⁻¹ * (w ^ 2)⁻¹ := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hw0 : 0 < w := by linarith
  have h1 : (u ^ 3)⁻¹ * u = (u ^ 2)⁻¹ := by field_simp
  have h2 : (v ^ 3)⁻¹ ≤ (v ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hv (by norm_num))
  have h3 : (w ^ 3)⁻¹ ≤ (w ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw (by norm_num))
  calc (u ^ 3)⁻¹ * (v ^ 3)⁻¹ * (w ^ 3)⁻¹ * u = ((u ^ 3)⁻¹ * u) * (v ^ 3)⁻¹ * (w ^ 3)⁻¹ := by ring
    _ ≤ (u ^ 2)⁻¹ * (v ^ 2)⁻¹ * (w ^ 2)⁻¹ := by
      rw [h1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3 (by positivity)
        (by positivity)

private theorem prod_cube_mul_le (z : Fin 3 → ℝ) (i : Fin 3) :
    (∏ j : Fin 3, ((1 + |z j|) ^ 3)⁻¹) * (1 + |z i|) ≤ ∏ j : Fin 3, ((1 + |z j|) ^ 2)⁻¹ := by
  have h : ∀ j, 1 ≤ 1 + |z j| := fun j => by linarith [abs_nonneg (z j)]
  simp only [Fin.prod_univ_three]
  fin_cases i
  · exact cube_aux _ _ _ (h 0) (h 1) (h 2)
  · have := cube_aux _ _ _ (h 1) (h 0) (h 2)
    simp only [Fin.isValue, Fin.mk_one]
    calc _ = ((1 + |z 1|) ^ 3)⁻¹ * ((1 + |z 0|) ^ 3)⁻¹ * ((1 + |z 2|) ^ 3)⁻¹ * (1 + |z 1|) := by
          ring
      _ ≤ _ := this
      _ = _ := by ring
  · have := cube_aux _ _ _ (h 2) (h 0) (h 1)
    simp only [Fin.isValue, Fin.reduceFinMk]
    calc _ = ((1 + |z 2|) ^ 3)⁻¹ * ((1 + |z 0|) ^ 3)⁻¹ * ((1 + |z 1|) ^ 3)⁻¹ * (1 + |z 2|) := by
          ring
      _ ≤ _ := this
      _ = _ := by ring

/-- Decay of the unit-scale parabolic kernel against a coordinate weight. -/
theorem exists_abs_parabolicKernel_one_mul_coord_le (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace,
      |parabolicKernel 1 z| * |z.2 i| ≤ C * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹ := by
  obtain ⟨Cg, hCg⟩ := heatKernel1D_one_decay 0
  obtain ⟨Ck, hCk⟩ := quarticKernel_one_decay 3
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
  have hk : ∀ j, |quarticKernel 1 (z.2 j)| ≤ Ck * ((1 + |z.2 j|) ^ 3)⁻¹ := by
    intro j
    have := hCk (z.2 j)
    rwa [decay_three_eq] at this
  have hq : |parabolicKernel 1 z| ≤ Cg * (Ck ^ 3 * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 3)⁻¹) := by
    unfold parabolicKernel
    rw [abs_mul, Finset.abs_prod]
    calc |heatKernel1D 1 z.1| * ∏ j, |quarticKernel 1 (z.2 j)|
        ≤ Cg * ∏ j : Fin 3, (Ck * ((1 + |z.2 j|) ^ 3)⁻¹) :=
          mul_le_mul hg (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hk j)
            (Finset.prod_nonneg fun j _ => abs_nonneg _) hCg0
      _ = Cg * (Ck ^ 3 * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 3)⁻¹) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hzi : |z.2 i| ≤ 1 + |z.2 i| := by linarith
  have hP0 : 0 ≤ ∏ j : Fin 3, ((1 + |z.2 j|) ^ 3)⁻¹ :=
    Finset.prod_nonneg fun j _ => by positivity
  calc |parabolicKernel 1 z| * |z.2 i|
      ≤ (Cg * (Ck ^ 3 * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 3)⁻¹)) * (1 + |z.2 i|) :=
        mul_le_mul hq hzi (abs_nonneg _) (by positivity)
    _ = Cg * Ck ^ 3 * ((∏ j : Fin 3, ((1 + |z.2 j|) ^ 3)⁻¹) * (1 + |z.2 i|)) := by ring
    _ ≤ Cg * Ck ^ 3 * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (prod_cube_mul_le z.2 i) (by positivity)

/-- Decay of the parabolic kernel at scales `t ≤ 1` against a coordinate weight; the weight gains
the factor `t^(1/4)`. -/
theorem exists_abs_parabolicKernel_mul_coord_le_decay (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ z : ParabolicSpace,
      |parabolicKernel t z| * |z.2 i| ≤
        C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_one_mul_coord_le i
  refine ⟨C, hC0, fun {t} ht ht1 z => ?_⟩
  have hc1 : 1 ≤ t ^ (-(1 / 4 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  have hcl : t ^ (-(1 / 4 : ℝ)) * t ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add ht]; norm_num
  have hl0 : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  set zd := parabolicDilate (t ^ (-(1 / 4 : ℝ))) z with hzd
  have hzi : |z.2 i| = t ^ (1 / 4 : ℝ) * |zd.2 i| := by
    simp only [hzd, parabolicDilate, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg (by linarith : 0 ≤ t ^ (-(1 / 4 : ℝ)))]
    calc |z.2 i| = (t ^ (-(1 / 4 : ℝ)) * t ^ (1 / 4 : ℝ)) * |z.2 i| := by rw [hcl, one_mul]
      _ = _ := by ring
  have hprod : ∏ j : Fin 3, ((1 + |zd.2 j|) ^ 2)⁻¹ ≤ ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹ := by
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    have hab : |z.2 j| ≤ |zd.2 j| := by
      simp only [hzd, parabolicDilate, Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [abs_of_nonneg (by linarith : 0 ≤ t ^ (-(1 / 4 : ℝ)))]
      nlinarith [abs_nonneg (z.2 j)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have h := hC zd
  rw [parabolicKernel_eq_scale ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), hzi]
  calc t ^ (-(5 / 4 : ℝ)) * |parabolicKernel 1 zd| * (t ^ (1 / 4 : ℝ) * |zd.2 i|)
      = t ^ (-(5 / 4 : ℝ)) * t ^ (1 / 4 : ℝ) * (|parabolicKernel 1 zd| * |zd.2 i|) := by ring
    _ ≤ t ^ (-(5 / 4 : ℝ)) * t ^ (1 / 4 : ℝ) * (C * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hprod hC0))
          (by positivity)
    _ = C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * ∏ j : Fin 3, ((1 + |z.2 j|) ^ 2)⁻¹ := by ring

/-- **Sup bound for the coordinate-weighted periodised semigroup kernel.** -/
theorem exists_abs_semigroupPeriodisedX_le (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x : ParabolicSpace) (u : SpaceTime),
      |semigroupPeriodisedX t x i u| ≤ B * (t ^ (1 / 4 : ℝ) * (((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_mul_coord_le_decay i
  obtain ⟨L, hL0, hL⟩ := exists_lattice_sum_le
  refine ⟨C * L, mul_nonneg hC0 hL0, fun {t} ht ht1 x u => ?_⟩
  rw [rpow_quarter_pow_five_inv ht]
  set a : Fin 3 → ℝ := fun j => x.2 j - torusRep u.2 j with ha
  set P : (Fin 3 → ℤ) → ℝ := fun k => ∏ j, ((1 + |a j + (k j : ℝ)|) ^ 2)⁻¹ with hP
  have hterm : ∀ k : Fin 3 → ℤ,
      |parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ)) *
        ((torusRep u.2 i + (k i : ℝ)) - x.2 i)| ≤
        C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * P (-k) := by
    intro k
    rw [abs_mul, parabolicSemigroup_kernel_eq]
    have hz : |((torusRep u.2 i + (k i : ℝ)) - x.2 i)| =
        |(x - (u.1, torusRep u.2 + fun j => (k j : ℝ))).2 i| := by
      simp only [Prod.snd_sub, Pi.sub_apply, Pi.add_apply]
      rw [abs_sub_comm]
    rw [hz]
    refine (hC ht ht1 _).trans (le_of_eq ?_)
    simp only [hP, ha, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show x.2 j - (torusRep u.2 j + (k j : ℝ)) = x.2 j - torusRep u.2 j + -(k j : ℝ) by ring]
  obtain ⟨hPs, hPL⟩ := hL a
  have hPs' : Summable (fun k => P (-k)) := ((Equiv.neg (Fin 3 → ℤ)).summable_iff (f := P)).2 hPs
  have hPt : ∑' k, P (-k) = ∑' k, P k := (Equiv.neg (Fin 3 → ℤ)).tsum_eq P
  have hsum : Summable (fun k : Fin 3 → ℤ =>
      |parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ)) *
        ((torusRep u.2 i + (k i : ℝ)) - x.2 i)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm (hPs'.mul_left _)
  unfold semigroupPeriodisedX
  calc |∑' k : Fin 3 → ℤ, parabolicSemigroup.kernel t x
          (u.1, torusRep u.2 + fun j => (k j : ℝ)) * ((torusRep u.2 i + (k i : ℝ)) - x.2 i)|
      ≤ ∑' k : Fin 3 → ℤ, |parabolicSemigroup.kernel t x
          (u.1, torusRep u.2 + fun j => (k j : ℝ)) * ((torusRep u.2 i + (k i : ℝ)) - x.2 i)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun k : Fin 3 → ℤ => parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun j => (k j : ℝ)) * ((torusRep u.2 i + (k i : ℝ)) - x.2 i))
          (by simpa using hsum)
    _ ≤ ∑' k : Fin 3 → ℤ, C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * P (-k) :=
        hsum.tsum_le_tsum hterm (hPs'.mul_left _)
    _ = C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * ∑' k : Fin 3 → ℤ, P k := by
        rw [tsum_mul_left, hPt]
    _ ≤ C * t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) * L :=
        mul_le_mul_of_nonneg_left hPL (by positivity)
    _ = C * L * (t ^ (1 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ))) := by ring

end RegularityStructures

end
