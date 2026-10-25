/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsSpatialPeriodisation
public import RegularityStructures.Torus.KernelBoundsGaussian

/-!
# Singular bounds for spatial Gaussian derivatives

The differentiated periodisation retains a centred Gaussian factor.  This is the
one-dimensional estimate needed to convert the lattice derivative majorants into
the parabolic singular power in K1′.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem gaussianOneDimMajorant_mono_of_le {a b : ℝ} (hba : b ≤ a) (n : ℤ) :
    gaussianOneDimMajorant a n ≤ gaussianOneDimMajorant b n := by
  unfold gaussianOneDimMajorant
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · simp only [hn, ↓reduceIte]
    apply add_le_add_right
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ)]
  · simp only [hn, ↓reduceIte, zero_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ)]

theorem gaussian_exp_center_shift_le_majorant {a : ℝ} (ha : 0 < a)
    {y : ℝ} (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (n : ℤ) :
    exp (-a * (y + (n : ℝ)) ^ 2) ≤
      exp (-a * y ^ 2) * gaussianOneDimMajorant a n := by
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · have hsq := sq_centered_add_int_ge hy n
    have hpoint : exp (-a * (y + (n : ℝ)) ^ 2) ≤ exp (-a * y ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsq]
    unfold gaussianOneDimMajorant
    simp only [hn, ↓reduceIte]
    calc
      exp (-a * (y + (n : ℝ)) ^ 2) ≤ exp (-a * y ^ 2) := hpoint
      _ ≤ exp (-a * y ^ 2) * (1 + exp (-(a / 4) * (n : ℝ) ^ 2)) := by
        calc
          exp (-a * y ^ 2) = exp (-a * y ^ 2) * 1 := by ring
          _ ≤ exp (-a * y ^ 2) *
              (1 + exp (-(a / 4) * (n : ℝ) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (exp_nonneg _)) (exp_nonneg _)
  · have hsq := sq_centered_add_int_tail_ge hy hn
    unfold gaussianOneDimMajorant
    simp only [hn, ↓reduceIte, zero_add]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hsq, sq_nonneg (n : ℝ)]

noncomputable def gaussianExpDerivativeBaseBound : ℝ :=
  max (Classical.choose (exists_bound_abs_pow_mul_expPowFun
    (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 1)) 0

theorem gaussianExpDerivativeBaseBound_nonneg : 0 ≤ gaussianExpDerivativeBaseBound := by
  unfold gaussianExpDerivativeBaseBound
  exact le_max_right _ _

theorem gaussianExpDerivativeBaseBound_spec (x : ℝ) :
    |x| * exp (-x ^ 2) ≤ gaussianExpDerivativeBaseBound := by
  have h := Classical.choose_spec (exists_bound_abs_pow_mul_expPowFun
    (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 1) x
  unfold gaussianExpDerivativeBaseBound
  calc
    |x| * exp (-x ^ 2) ≤ Classical.choose (exists_bound_abs_pow_mul_expPowFun
        (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 1) := by
      simpa only [pow_one, expPowFun, Nat.reduceMul, one_mul] using h
    _ ≤ max (Classical.choose (exists_bound_abs_pow_mul_expPowFun
        (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 1)) 0 :=
      le_max_left _ _

theorem gaussian_expPowFun_one_deriv_center_bound {a : ℝ} (ha : 0 < a) :
    ∀ x : ℝ, |iteratedDeriv 1 (expPowFun a 2) x| ≤
      2 * √(2 * a) * gaussianExpDerivativeBaseBound *
        exp (-(a / 2) * x ^ 2) := by
  intro x
  let u : ℝ := √(a / 2) * x
  have hu : |u| * exp (-u ^ 2) ≤ gaussianExpDerivativeBaseBound := by
    exact gaussianExpDerivativeBaseBound_spec u
  rw [iteratedDeriv_one, (hasDerivAt_expPowFun a 2 x).deriv]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  unfold expPowFun
  have habs : |-(a * 2 * x) * exp (-(a * x ^ 2))| =
      2 * a * |x| * exp (-(a * x ^ 2)) := by
    rw [abs_mul, abs_neg, abs_mul,
      abs_of_pos (mul_pos ha (by norm_num : (0 : ℝ) < 2))]
    simp only [abs_of_nonneg (by positivity : 0 ≤ exp (-(a * x ^ 2)))]
    ring
  rw [habs]
  have hax : a * x ^ 2 = 2 * u ^ 2 := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ a / 2)]
    ring
  have hfactor : 2 * a * |x| * exp (-(a * x ^ 2)) =
      2 * √(2 * a) * (|u| * exp (-u ^ 2)) * exp (-u ^ 2) := by
    rw [hax]
    have hux : |u| = √(a / 2) * |x| := by
      dsimp [u]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ √(a / 2))]
    rw [hux]
    have hsqrt : √(2 * a) * √(a / 2) = a := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * a)]
      rw [show 2 * a * (a / 2) = a ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_pos ha]
    rw [show -(2 * u ^ 2) = -u ^ 2 + -u ^ 2 by ring, Real.exp_add]
    calc
      2 * a * |x| * (exp (-u ^ 2) * exp (-u ^ 2)) =
          2 * (√(2 * a) * √(a / 2)) * |x| *
            (exp (-u ^ 2) * exp (-u ^ 2)) := by rw [hsqrt]
      _ = 2 * √(2 * a) * (√(a / 2) * |x| * exp (-u ^ 2)) *
            exp (-u ^ 2) := by ring
  have hu_sq : u ^ 2 = (a / 2) * x ^ 2 := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ a / 2)]
  have hu' : |u| * exp (-(a / 2) * x ^ 2) ≤ gaussianExpDerivativeBaseBound := by
    calc
      |u| * exp (-(a / 2) * x ^ 2) =
          |u| * exp (-((a / 2) * x ^ 2)) := by
            congr 2
            ring
      _ = |u| * exp (-u ^ 2) := by rw [hu_sq]
      _ ≤ gaussianExpDerivativeBaseBound := hu
  have hexp : exp (-u ^ 2) = exp (-(a / 2) * x ^ 2) := by
    calc
      exp (-u ^ 2) = exp (-((a / 2) * x ^ 2)) := by rw [hu_sq]
      _ = exp (-(a / 2) * x ^ 2) := by
        congr 1
        ring
  rw [hfactor, hexp]
  gcongr

noncomputable def gaussianExpSecondDerivativeBaseBound : ℝ :=
  max (Classical.choose (exists_bound_abs_pow_mul_expPowFun
    (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 2)) 0

theorem gaussianExpSecondDerivativeBaseBound_nonneg :
    0 ≤ gaussianExpSecondDerivativeBaseBound := by
  unfold gaussianExpSecondDerivativeBaseBound
  exact le_max_right _ _

theorem gaussianExpSecondDerivativeBaseBound_spec (x : ℝ) :
    |x| ^ 2 * exp (-x ^ 2) ≤ gaussianExpSecondDerivativeBaseBound := by
  have h := Classical.choose_spec (exists_bound_abs_pow_mul_expPowFun
    (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 2) x
  unfold gaussianExpSecondDerivativeBaseBound
  calc
    |x| ^ 2 * exp (-x ^ 2) ≤ Classical.choose (exists_bound_abs_pow_mul_expPowFun
        (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 2) := by
      simpa only [expPowFun, Nat.reduceMul, one_mul] using h
    _ ≤ max (Classical.choose (exists_bound_abs_pow_mul_expPowFun
        (c := (1 : ℝ)) (by norm_num) (j := 1) (by norm_num) 2)) 0 :=
      le_max_left _ _

theorem gaussian_expPowFun_two_deriv_center_bound {a : ℝ} (ha : 0 < a) :
    ∀ x : ℝ, |iteratedDeriv 2 (expPowFun a 2) x| ≤
      2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1) *
        exp (-(a / 2) * x ^ 2) := by
  intro x
  let u : ℝ := √(a / 2) * x
  have hu_sq : u ^ 2 = (a / 2) * x ^ 2 := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ a / 2)]
  have hu : u ^ 2 * exp (-u ^ 2) ≤ gaussianExpSecondDerivativeBaseBound := by
    have h := gaussianExpSecondDerivativeBaseBound_spec u
    simpa only [sq_abs] using h
  rw [iteratedDeriv_two_expPowFun]
  unfold expPowFun
  have hlinear :
      |(4 * a ^ 2 * x ^ 2 - 2 * a) * exp (-(a * x ^ 2))| ≤
        4 * a ^ 2 * x ^ 2 * exp (-(a * x ^ 2)) +
          2 * a * exp (-(a * x ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (exp_nonneg _)]
    have hsub := abs_sub_le (4 * a ^ 2 * x ^ 2) 0 (2 * a)
    have hsub' : |4 * a ^ 2 * x ^ 2 - 2 * a| ≤
        4 * a ^ 2 * x ^ 2 + 2 * a := by
      simpa only [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ 4 * a ^ 2 * x ^ 2),
        abs_of_pos (by positivity : 0 < 2 * a)] using hsub
    calc
      |4 * a ^ 2 * x ^ 2 - 2 * a| * exp (-(a * x ^ 2)) ≤
          (4 * a ^ 2 * x ^ 2 + 2 * a) * exp (-(a * x ^ 2)) :=
        mul_le_mul_of_nonneg_right hsub' (exp_nonneg _)
      _ = _ := by ring_nf
  have hA : 4 * a ^ 2 * x ^ 2 * exp (-(a * x ^ 2)) ≤
      8 * a * gaussianExpSecondDerivativeBaseBound *
        exp (-(a / 2) * x ^ 2) := by
    have hexp : exp (-(a * x ^ 2)) = exp (-u ^ 2) * exp (-u ^ 2) := by
      rw [show -(a * x ^ 2) = -u ^ 2 + -u ^ 2 by rw [hu_sq]; ring,
        Real.exp_add]
    rw [hexp]
    have hmul : 8 * a * (u ^ 2 * exp (-u ^ 2)) * exp (-u ^ 2) ≤
        8 * a * gaussianExpSecondDerivativeBaseBound * exp (-u ^ 2) := by
      gcongr
    calc
      4 * a ^ 2 * x ^ 2 * (exp (-u ^ 2) * exp (-u ^ 2)) =
          8 * a * (u ^ 2 * exp (-u ^ 2)) * exp (-u ^ 2) := by
        rw [hu_sq]
        ring
      _ ≤ 8 * a * gaussianExpSecondDerivativeBaseBound * exp (-u ^ 2) := hmul
      _ = 8 * a * gaussianExpSecondDerivativeBaseBound *
          exp (-(a / 2) * x ^ 2) := by
        rw [hu_sq]
        congr 1
        ring_nf
  have hB : 2 * a * exp (-(a * x ^ 2)) ≤
      2 * a * exp (-(a / 2) * x ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  calc
    |(4 * a ^ 2 * x ^ 2 - 2 * a) * exp (-(a * x ^ 2))| ≤
        4 * a ^ 2 * x ^ 2 * exp (-(a * x ^ 2)) +
          2 * a * exp (-(a * x ^ 2)) := hlinear
    _ ≤ 8 * a * gaussianExpSecondDerivativeBaseBound *
          exp (-(a / 2) * x ^ 2) +
        2 * a * exp (-(a / 2) * x ^ 2) := add_le_add hA hB
    _ = 2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1) *
        exp (-(a / 2) * x ^ 2) := by ring

theorem exp_prod_one_center_bound {i : Fin 3} {E T : Fin 3 → ℝ}
    (hE0 : ∀ j, 0 ≤ E j) (hE : ∀ j, E j ≤ T j)
    (hEdouble : ∀ j, j ≠ i → E j * E j ≤ T j)
    (hT : ∀ j, 0 ≤ T j) :
    E i * (∏ j, if j = i then 1 else E j * E j) ≤ ∏ j, T j := by
  fin_cases i
  · simp [Fin.prod_univ_three]
    have h01 : E 0 * (E 1 * E 1) ≤ T 0 * T 1 := by
      exact mul_le_mul (hE 0) (hEdouble 1 (by decide))
        (mul_nonneg (hE0 1) (hE0 1)) (hT 0)
    calc
      E 0 * ((E 1 * E 1) * (E 2 * E 2)) =
          (E 0 * (E 1 * E 1)) * (E 2 * E 2) := by ring
      _ ≤ (T 0 * T 1) * (E 2 * E 2) :=
        mul_le_mul_of_nonneg_right h01 (mul_nonneg (hE0 2) (hE0 2))
      _ ≤ (T 0 * T 1) * T 2 :=
        mul_le_mul_of_nonneg_left (hEdouble 2 (by decide)) (mul_nonneg (hT 0) (hT 1))
      _ = _ := by ring
  · simp [Fin.prod_univ_three]
    have h10 : (E 0 * E 0) * E 1 ≤ T 0 * T 1 := by
      exact mul_le_mul (hEdouble 0 (by decide)) (hE 1)
        (hE0 1) (hT 0)
    calc
      E 1 * ((E 0 * E 0) * (E 2 * E 2)) =
          ((E 0 * E 0) * E 1) * (E 2 * E 2) := by ring
      _ ≤ (T 0 * T 1) * (E 2 * E 2) :=
        mul_le_mul_of_nonneg_right h10 (mul_nonneg (hE0 2) (hE0 2))
      _ ≤ (T 0 * T 1) * T 2 :=
        mul_le_mul_of_nonneg_left (hEdouble 2 (by decide)) (mul_nonneg (hT 0) (hT 1))
      _ = _ := by ring
  · simp [Fin.prod_univ_three]
    have h21 : (E 0 * E 0) * (E 1 * E 1) ≤ T 0 * T 1 := by
      exact mul_le_mul (hEdouble 0 (by decide)) (hEdouble 1 (by decide))
        (mul_nonneg (hE0 1) (hE0 1)) (hT 0)
    calc
      E 2 * ((E 0 * E 0) * (E 1 * E 1)) =
          ((E 0 * E 0) * (E 1 * E 1)) * E 2 := by ring
      _ ≤ (T 0 * T 1) * E 2 :=
        mul_le_mul_of_nonneg_right h21 (hE0 2)
      _ ≤ (T 0 * T 1) * T 2 :=
        mul_le_mul_of_nonneg_left (hE 2) (mul_nonneg (hT 0) (hT 1))
      _ = _ := by ring

theorem gaussKernelSpaceLine_first_deriv_center_bound {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (k : Fin 3 → ℤ) :
    |iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)| ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound) *
        ∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
          gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) := by
  let a : ℝ := (4 * t)⁻¹
  let b : ℝ := a / 2
  let E : Fin 3 → ℝ := fun j => exp (-b * (y j + (k j : ℝ)) ^ 2)
  let T : Fin 3 → ℝ := fun j =>
    exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hy' : ∀ j : Fin 3, y j ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro j
    simpa only [neg_div] using hy j
  have hE0 : ∀ j, 0 ≤ E j := by
    intro j
    exact exp_nonneg _
  have hE : ∀ j, E j ≤ T j := by
    intro j
    exact gaussian_exp_center_shift_le_majorant hb (hy' j) (k j)
  have hEone : ∀ j, E j ≤ 1 := by
    intro j
    dsimp [E]
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (y j + (k j : ℝ))]
  have hEdouble : ∀ j, j ≠ i → E j * E j ≤ T j := by
    intro j hji
    calc
      E j * E j ≤ 1 * E j :=
        mul_le_mul_of_nonneg_right (hEone j) (hE0 j)
      _ ≤ 1 * T j := mul_le_mul_of_nonneg_left (hE j) (by positivity)
      _ = T j := by ring
  have hT : ∀ j, 0 ≤ T j := by
    intro j
    exact mul_nonneg (exp_nonneg _) (gaussianOneDimMajorant_nonneg _)
  have hprod : E i * (∏ j, if j = i then 1 else E j * E j) ≤ ∏ j, T j :=
    exp_prod_one_center_bound hE0 hE hEdouble hT
  have hD := gaussian_expPowFun_one_deriv_center_bound ha (y i + (k i : ℝ))
  have hcoeff : 0 ≤ gaussKernelSpaceLineCoeff t i y k := by
    unfold gaussKernelSpaceLineCoeff
    positivity
  rw [iteratedDeriv_gaussKernelSpaceLine, abs_mul, abs_of_nonneg hcoeff]
  have hfactor : ∀ j, j ≠ i →
      exp (-a * (y j + (k j : ℝ)) ^ 2) = E j * E j := by
    intro j _
    dsimp [E, b]
    rw [show -a * (y j + (k j : ℝ)) ^ 2 =
        -(a / 2) * (y j + (k j : ℝ)) ^ 2 +
          -(a / 2) * (y j + (k j : ℝ)) ^ 2 by ring, Real.exp_add]
  have hprod_coeff :
      (∏ j, if j = i then 1 else
        exp (-a * (y j + (k j : ℝ)) ^ 2)) =
        ∏ j, if j = i then 1 else E j * E j := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp only [ite_eq_right hji]
      convert hfactor j hji using 1
  have hcoeff_eq :
      gaussKernelSpaceLineCoeff t i y k *
          (2 * √(2 * a) * gaussianExpDerivativeBaseBound * E i) =
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (2 * √(2 * a) * gaussianExpDerivativeBaseBound) *
          (E i * (∏ j, if j = i then 1 else E j * E j)) := by
    unfold gaussKernelSpaceLineCoeff
    rw [hprod_coeff]
    ring
  have hbase : 0 ≤ gaussianExpDerivativeBaseBound :=
    gaussianExpDerivativeBaseBound_nonneg
  have hDnonneg : 0 ≤ 2 * √(2 * a) * gaussianExpDerivativeBaseBound := by
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hbase
  have hcoefnonneg : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
      (2 * √(2 * a) * gaussianExpDerivativeBaseBound) := by
    exact mul_nonneg (by positivity) hDnonneg
  calc
    gaussKernelSpaceLineCoeff t i y k *
        |iteratedDeriv 1 (expPowFun a 2) (y i + (k i : ℝ))| ≤
        gaussKernelSpaceLineCoeff t i y k *
          (2 * √(2 * a) * gaussianExpDerivativeBaseBound * E i) :=
      mul_le_mul_of_nonneg_left hD hcoeff
    _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * a) * gaussianExpDerivativeBaseBound) *
        (E i * (∏ j, if j = i then 1 else E j * E j)) := by
      rw [hcoeff_eq]
    _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * a) * gaussianExpDerivativeBaseBound) * ∏ j, T j :=
      mul_le_mul_of_nonneg_left hprod hcoefnonneg
    _ = _ := by
      simp only [T, Fin.prod_univ_three]
      rfl

theorem gaussKernelSpaceLine_second_deriv_center_bound {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (k : Fin 3 → ℤ) :
    |iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i)| ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * ((4 * t)⁻¹) * (4 * gaussianExpSecondDerivativeBaseBound + 1)) *
        ∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
          gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) := by
  let a : ℝ := (4 * t)⁻¹
  let b : ℝ := a / 2
  let E : Fin 3 → ℝ := fun j => exp (-b * (y j + (k j : ℝ)) ^ 2)
  let T : Fin 3 → ℝ := fun j =>
    exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hy' : ∀ j : Fin 3, y j ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro j
    simpa only [neg_div] using hy j
  have hE0 : ∀ j, 0 ≤ E j := by
    intro j
    exact exp_nonneg _
  have hE : ∀ j, E j ≤ T j := by
    intro j
    exact gaussian_exp_center_shift_le_majorant hb (hy' j) (k j)
  have hEone : ∀ j, E j ≤ 1 := by
    intro j
    dsimp [E]
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (y j + (k j : ℝ))]
  have hEdouble : ∀ j, j ≠ i → E j * E j ≤ T j := by
    intro j hji
    calc
      E j * E j ≤ 1 * E j :=
        mul_le_mul_of_nonneg_right (hEone j) (hE0 j)
      _ ≤ 1 * T j := mul_le_mul_of_nonneg_left (hE j) (by positivity)
      _ = T j := by ring
  have hT : ∀ j, 0 ≤ T j := by
    intro j
    exact mul_nonneg (exp_nonneg _) (gaussianOneDimMajorant_nonneg _)
  have hprod : E i * (∏ j, if j = i then 1 else E j * E j) ≤ ∏ j, T j :=
    exp_prod_one_center_bound hE0 hE hEdouble hT
  have hD := gaussian_expPowFun_two_deriv_center_bound ha (y i + (k i : ℝ))
  have hcoeff : 0 ≤ gaussKernelSpaceLineCoeff t i y k := by
    unfold gaussKernelSpaceLineCoeff
    positivity
  rw [iteratedDeriv_gaussKernelSpaceLine, abs_mul, abs_of_nonneg hcoeff]
  have hfactor : ∀ j, j ≠ i →
      exp (-a * (y j + (k j : ℝ)) ^ 2) = E j * E j := by
    intro j _
    dsimp [E, b]
    rw [show -a * (y j + (k j : ℝ)) ^ 2 =
        -(a / 2) * (y j + (k j : ℝ)) ^ 2 +
          -(a / 2) * (y j + (k j : ℝ)) ^ 2 by ring, Real.exp_add]
  have hprod_coeff :
      (∏ j, if j = i then 1 else
        exp (-a * (y j + (k j : ℝ)) ^ 2)) =
        ∏ j, if j = i then 1 else E j * E j := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp only [ite_eq_right hji]
      convert hfactor j hji using 1
  have hcoeff_eq :
      gaussKernelSpaceLineCoeff t i y k *
          (2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1) * E i) =
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1)) *
          (E i * (∏ j, if j = i then 1 else E j * E j)) := by
    unfold gaussKernelSpaceLineCoeff
    rw [hprod_coeff]
    ring
  have hbase : 0 ≤ 2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (by nlinarith [gaussianExpSecondDerivativeBaseBound_nonneg])
  calc
    gaussKernelSpaceLineCoeff t i y k *
        |iteratedDeriv 2 (expPowFun a 2) (y i + (k i : ℝ))| ≤
        gaussKernelSpaceLineCoeff t i y k *
          (2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1) * E i) :=
      mul_le_mul_of_nonneg_left hD hcoeff
    _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1)) *
        (E i * (∏ j, if j = i then 1 else E j * E j)) := by
      rw [hcoeff_eq]
    _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * a * (4 * gaussianExpSecondDerivativeBaseBound + 1)) * ∏ j, T j :=
      mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (by positivity) hbase)
    _ = _ := by
      simp only [Fin.prod_univ_three]
      rfl

noncomputable def gaussianProductMajorantSum : ℝ :=
  ∑' k : Fin 3 → ℤ, ∏ i, gaussianOneDimMajorant (1 / 8) (k i)

theorem summable_gaussianProductMajorant :
    Summable (fun k : Fin 3 → ℤ => ∏ i, gaussianOneDimMajorant (1 / 8) (k i)) := by
  exact summable_pi_fin3_prod
    (summable_gaussianOneDimMajorant (by norm_num)) gaussianOneDimMajorant_nonneg

theorem nonneg_gaussianProductMajorantSum : 0 ≤ gaussianProductMajorantSum := by
  unfold gaussianProductMajorantSum
  exact tsum_nonneg fun k =>
    Finset.prod_nonneg fun i _ => gaussianOneDimMajorant_nonneg _

theorem gaussianProductMajorant_tsum_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∑' k : Fin 3 → ℤ, ∏ i, gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k i) ≤
      gaussianProductMajorantSum := by
  have hinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1
  have hb : (1 / 8 : ℝ) ≤ ((4 * t)⁻¹) / 2 := by
    calc
      (1 / 8 : ℝ) = (1 / 8 : ℝ) * 1 := by ring
      _ ≤ (1 / 8 : ℝ) * t⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = ((4 * t)⁻¹) / 2 := by
        field_simp [ne_of_gt ht]
        norm_num
  have hleft : Summable (fun k : Fin 3 → ℤ =>
      ∏ i, gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k i)) := by
    exact summable_pi_fin3_prod
      (summable_gaussianOneDimMajorant (by positivity)) gaussianOneDimMajorant_nonneg
  have hright : Summable (fun k : Fin 3 → ℤ =>
      ∏ i, gaussianOneDimMajorant (1 / 8) (k i)) := summable_gaussianProductMajorant
  apply hleft.tsum_le_tsum
  · intro k
    apply Finset.prod_le_prod₀
    · intro i hi
      exact gaussianOneDimMajorant_nonneg _
    · intro i hi
      exact gaussianOneDimMajorant_mono_of_le hb (k i)
  · exact hright

noncomputable def gaussKernelSpaceLine_first_deriv_tsum (t : ℝ) (i : Fin 3)
    (y : Fin 3 → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℤ, iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)

noncomputable def firstSpatialDerivativeScale (t : ℝ) : ℝ := ((4 * t)⁻¹) / 2

noncomputable def firstSpatialDerivativeCoefficient (t : ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) *
    (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound)

theorem firstSpatialDerivativeCoefficient_mul_sq {t : ℝ} (ht : 0 < t) :
    firstSpatialDerivativeCoefficient t * t ^ 2 =
      firstSpatialDerivativeCoefficient 1 := by
  unfold firstSpatialDerivativeCoefficient
  have ht0 : 0 ≤ t := ht.le
  have harg : 2 * (4 * t)⁻¹ = (1 / 2 : ℝ) * t⁻¹ := by
    field_simp [ne_of_gt ht]
    ring
  rw [show 4 * π * t = (4 * π) * t by ring,
    Real.mul_rpow (by positivity) ht0, harg,
    Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht0)]
  rw [Real.inv_rpow ht0]
  rw [← Real.rpow_neg ht0]
  have hpow : t ^ (-(3 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) * t ^ 2 = 1 := by
    calc
      _ = t ^ (-(3 : ℝ) / 2 + -(1 : ℝ) / 2) * t ^ 2 := by
        rw [← Real.rpow_add ht]
      _ = t ^ (-(3 : ℝ) / 2 + -(1 : ℝ) / 2 + 2) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_add ht (-(3 : ℝ) / 2 + -(1 : ℝ) / 2) 2).symm
      _ = 1 := by norm_num
  calc
    _ = 4 ^ (-(3 : ℝ) / 2) * π ^ (-(3 : ℝ) / 2) *
        (2 * ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) * gaussianExpDerivativeBaseBound) *
        (t ^ (-(3 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) * t ^ 2) := by ring_nf
    _ = 4 ^ (-(3 : ℝ) / 2) * π ^ (-(3 : ℝ) / 2) *
        (2 * ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) * gaussianExpDerivativeBaseBound) := by
      rw [hpow]
      ring
    _ = _ := by
      have hsqrt : √(2 * (4 * (1 : ℝ))⁻¹) =
          (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
        norm_num [Real.sqrt_eq_rpow]
      rw [hsqrt, show 4 * π * 1 = π * 4 by ring]
      have hpi : 4 ^ (-(3 : ℝ) / 2) * π ^ (-(3 : ℝ) / 2) =
          (π * 4) ^ (-(3 : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity) (by norm_num)]
        norm_num
        ring
      rw [← hpi]

theorem exists_exp_neg_sq_mul_one_add_pow_four_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_abs_pow_mul_expPowFun
    (c := (1 / 8 : ℝ)) (by norm_num) (j := 1) (by norm_num) 4
  let B' : ℝ := max B 0
  let C : ℝ := max (2 ^ (4 : ℕ) : ℝ) (2 ^ (4 : ℕ) * B')
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hB'r : r ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ B' := by
    calc
      r ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ B := by
        simpa [abs_of_nonneg hr, expPowFun] using hB r
      _ ≤ B' := le_max_left _ _
  have hexp : exp (-(1 / 8 : ℝ) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg r]
  by_cases hsmall : r ≤ 1
  · have hpow : (1 + r) ^ 4 ≤ (2 : ℝ) ^ 4 := by
      have hlin : 1 + r ≤ 2 := by linarith
      gcongr
    calc
      (1 + r) ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤
          (2 : ℝ) ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (exp_nonneg _)
      _ ≤ (2 : ℝ) ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ C := by
        dsimp [C]
        norm_num
  · have hlarge : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hpow : (1 + r) ^ 4 ≤ (2 : ℝ) ^ 4 * r ^ 4 := by
      have hlin : 1 + r ≤ 2 * r := by linarith
      calc
        (1 + r) ^ 4 ≤ (2 * r) ^ 4 := by gcongr
        _ = (2 : ℝ) ^ 4 * r ^ 4 := by ring
    calc
      (1 + r) ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤
          (2 : ℝ) ^ 4 * r ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (exp_nonneg _)
      _ ≤ (2 : ℝ) ^ 4 * B' := by
        calc
          (2 : ℝ) ^ 4 * r ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2) =
              (2 : ℝ) ^ 4 * (r ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2)) := by ring
          _ ≤ (2 : ℝ) ^ 4 * B' :=
            mul_le_mul_of_nonneg_left hB'r (by positivity)
      _ ≤ C := le_max_right _ _

theorem exists_parabolic_gaussian_power_four_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 ≤ s →
      (√t + √s) ^ 4 * exp (-((1 / 8 : ℝ) / t) * s) ≤ C * t ^ 2 := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_exp_neg_sq_mul_one_add_pow_four_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro t ht s hs
  let q : ℝ := √t
  let r : ℝ := √s / q
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hq2 : q ^ 2 = t := by
    dsimp [q]
    exact Real.sq_sqrt ht.le
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sqrt_nonneg _) hq.le
  have hrs : r ^ 2 = s / t := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hs, Real.sq_sqrt ht.le]
  have hsum : √t + √s = q * (1 + r) := by
    dsimp [q, r]
    field_simp [ne_of_gt hq]
  have hexp : -((1 / 8 : ℝ) / t) * s = -(1 / 8 : ℝ) * r ^ 2 := by
    rw [hrs]
    field_simp [ne_of_gt ht]
  have hq4 : q ^ 4 = t ^ 2 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hq2]
  calc
    (√t + √s) ^ 4 * exp (-((1 / 8 : ℝ) / t) * s) =
        q ^ 4 * ((1 + r) ^ 4 * exp (-(1 / 8 : ℝ) * r ^ 2)) := by
      rw [hsum, hexp]
      ring
    _ ≤ q ^ 4 * C₀ := by
      exact mul_le_mul_of_nonneg_left (hC r hr) (by positivity)
    _ = C₀ * t ^ 2 := by rw [hq4]; ring

theorem firstSpatialDerivativeCoefficient_parabolic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 ≤ s →
      (√t + √s) ^ 4 *
          (firstSpatialDerivativeCoefficient t *
            exp (-firstSpatialDerivativeScale t * s)) ≤ C := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_parabolic_gaussian_power_four_bound
  have hcoeff1 : 0 ≤ firstSpatialDerivativeCoefficient 1 := by
    unfold firstSpatialDerivativeCoefficient
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _))
        gaussianExpDerivativeBaseBound_nonneg)
  refine ⟨C₀ * firstSpatialDerivativeCoefficient 1, mul_nonneg hC₀ hcoeff1, ?_⟩
  intro t ht s hs
  have hcoeff : 0 ≤ firstSpatialDerivativeCoefficient t := by
    unfold firstSpatialDerivativeCoefficient
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _))
        gaussianExpDerivativeBaseBound_nonneg)
  have hscale : firstSpatialDerivativeCoefficient t * t ^ 2 =
      firstSpatialDerivativeCoefficient 1 := firstSpatialDerivativeCoefficient_mul_sq ht
  have hscale' : firstSpatialDerivativeScale t = (1 / 8 : ℝ) / t := by
    unfold firstSpatialDerivativeScale
    field_simp [ne_of_gt ht]
    ring
  rw [hscale']
  calc
    (√t + √s) ^ 4 *
        (firstSpatialDerivativeCoefficient t * exp (-((1 / 8 : ℝ) / t) * s)) =
        firstSpatialDerivativeCoefficient t *
          ((√t + √s) ^ 4 * exp (-((1 / 8 : ℝ) / t) * s)) := by ring
    _ ≤ firstSpatialDerivativeCoefficient t * (C₀ * t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hC t ht s hs) hcoeff
    _ = C₀ * firstSpatialDerivativeCoefficient 1 := by
      calc
        firstSpatialDerivativeCoefficient t * (C₀ * t ^ 2) =
            C₀ * (firstSpatialDerivativeCoefficient t * t ^ 2) := by ring
        _ = C₀ * firstSpatialDerivativeCoefficient 1 := by rw [hscale]

theorem exists_exp_neg_sq_mul_one_add_pow_five_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_abs_pow_mul_expPowFun
    (c := (1 / 8 : ℝ)) (by norm_num) (j := 1) (by norm_num) 5
  let B' : ℝ := max B 0
  let C : ℝ := max (2 ^ (5 : ℕ) : ℝ) (2 ^ (5 : ℕ) * B')
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hB'r : r ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ B' := by
    calc
      r ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤ B := by
        simpa [abs_of_nonneg hr, expPowFun] using hB r
      _ ≤ B' := le_max_left _ _
  have hexp : exp (-(1 / 8 : ℝ) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg r]
  by_cases hsmall : r ≤ 1
  · have hpow : (1 + r) ^ 5 ≤ (2 : ℝ) ^ 5 := by
      have hlin : 1 + r ≤ 2 := by linarith
      gcongr
    calc
      (1 + r) ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤
          (2 : ℝ) ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (exp_nonneg _)
      _ ≤ (2 : ℝ) ^ 5 * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ C := by
        dsimp [C]
        norm_num
  · have hlarge : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hpow : (1 + r) ^ 5 ≤ (2 : ℝ) ^ 5 * r ^ 5 := by
      have hlin : 1 + r ≤ 2 * r := by linarith
      calc
        (1 + r) ^ 5 ≤ (2 * r) ^ 5 := by gcongr
        _ = (2 : ℝ) ^ 5 * r ^ 5 := by ring
    calc
      (1 + r) ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) ≤
          (2 : ℝ) ^ 5 * r ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (exp_nonneg _)
      _ ≤ (2 : ℝ) ^ 5 * B' := by
        calc
          (2 : ℝ) ^ 5 * r ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2) =
              (2 : ℝ) ^ 5 * (r ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2)) := by ring
          _ ≤ (2 : ℝ) ^ 5 * B' :=
            mul_le_mul_of_nonneg_left hB'r (by positivity)
      _ ≤ C := le_max_right _ _

theorem exists_parabolic_gaussian_power_five_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 ≤ s →
      (√t + √s) ^ 5 * exp (-((1 / 8 : ℝ) / t) * s) ≤ C * t ^ 2 * √t := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_exp_neg_sq_mul_one_add_pow_five_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro t ht s hs
  let q : ℝ := √t
  let r : ℝ := √s / q
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hq2 : q ^ 2 = t := by
    dsimp [q]
    exact Real.sq_sqrt ht.le
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sqrt_nonneg _) hq.le
  have hrs : r ^ 2 = s / t := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hs, Real.sq_sqrt ht.le]
  have hsum : √t + √s = q * (1 + r) := by
    dsimp [q, r]
    field_simp [ne_of_gt hq]
  have hexp : -((1 / 8 : ℝ) / t) * s = -(1 / 8 : ℝ) * r ^ 2 := by
    rw [hrs]
    field_simp [ne_of_gt ht]
  have hq4 : q ^ 4 = t ^ 2 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hq2]
  have hq5 : q ^ 5 = t ^ 2 * q := by
    calc
      q ^ 5 = q ^ 4 * q := by ring
      _ = t ^ 2 * q := by rw [hq4]
  calc
    (√t + √s) ^ 5 * exp (-((1 / 8 : ℝ) / t) * s) =
        q ^ 5 * ((1 + r) ^ 5 * exp (-(1 / 8 : ℝ) * r ^ 2)) := by
      rw [hsum, hexp]
      ring
    _ ≤ q ^ 5 * C₀ := by
      exact mul_le_mul_of_nonneg_left (hC r hr) (by positivity)
    _ = C₀ * t ^ 2 * √t := by rw [hq5]; dsimp [q]; ring

noncomputable def secondSpatialDerivativeCoefficient (t : ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) *
    (2 * ((4 * t)⁻¹) * (4 * gaussianExpSecondDerivativeBaseBound + 1))

theorem secondSpatialDerivativeCoefficient_mul_sq_mul_sqrt {t : ℝ} (ht : 0 < t) :
    secondSpatialDerivativeCoefficient t * (t ^ 2 * √t) =
      secondSpatialDerivativeCoefficient 1 := by
  unfold secondSpatialDerivativeCoefficient
  have ht0 : 0 ≤ t := ht.le
  have hprefeq : (4 * π * t) ^ (-(3 : ℝ) / 2) =
      (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
    rw [show 4 * π * t = (4 * π) * t by ring,
      Real.mul_rpow (by positivity) ht0]
  have hinv : (4 * t)⁻¹ = (4 : ℝ)⁻¹ * t⁻¹ := by
    field_simp
  have htinv : t⁻¹ = t ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg ht.le, Real.rpow_one]
  have htsqrt : √t = t ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
  rw [hprefeq, hinv, htinv, htsqrt]
  have hcancel : t ^ (-(3 : ℝ) / 2) * t ^ (-(1 : ℝ)) *
      t ^ 2 * t ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_natCast]
    calc
      _ = t ^ (-(3 : ℝ) / 2 + -(1 : ℝ)) * t ^ (2 : ℝ) *
          t ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add ht]
        norm_num
      _ = t ^ (-(3 : ℝ) / 2 + -(1 : ℝ) + 2) *
          t ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_add ht]
      _ = t ^ (-(3 : ℝ) / 2 + -(1 : ℝ) + 2 + (1 : ℝ) / 2) := by
        rw [← Real.rpow_add ht]
      _ = 1 := by norm_num
  calc
    (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) *
        (2 * (4⁻¹ * t ^ (-(1 : ℝ))) *
          (4 * gaussianExpSecondDerivativeBaseBound + 1)) *
        (t ^ 2 * t ^ ((1 : ℝ) / 2)) =
        (4 * π) ^ (-(3 : ℝ) / 2) *
          (2 * 4⁻¹ * (4 * gaussianExpSecondDerivativeBaseBound + 1)) *
          (t ^ (-(3 : ℝ) / 2) * t ^ (-(1 : ℝ)) *
            t ^ 2 * t ^ ((1 : ℝ) / 2)) := by ring
    _ = (4 * π) ^ (-(3 : ℝ) / 2) *
          (2 * 4⁻¹ * (4 * gaussianExpSecondDerivativeBaseBound + 1)) := by
      rw [hcancel]
      ring
    _ = (4 * π * (1 : ℝ)) ^ (-(3 : ℝ) / 2) *
          (2 * ((4 * (1 : ℝ))⁻¹) *
            (4 * gaussianExpSecondDerivativeBaseBound + 1)) := by
      norm_num

theorem secondSpatialDerivativeCoefficient_parabolic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 ≤ s →
      (√t + √s) ^ 5 *
          (secondSpatialDerivativeCoefficient t *
            exp (-(((4 * t)⁻¹) / 2) * s)) ≤ C := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_parabolic_gaussian_power_five_bound
  have hcoeff1 : 0 ≤ secondSpatialDerivativeCoefficient 1 := by
    unfold secondSpatialDerivativeCoefficient
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (by nlinarith [gaussianExpSecondDerivativeBaseBound_nonneg]))
  refine ⟨C₀ * secondSpatialDerivativeCoefficient 1, mul_nonneg hC₀ hcoeff1, ?_⟩
  intro t ht s hs
  have hcoeff : 0 ≤ secondSpatialDerivativeCoefficient t := by
    unfold secondSpatialDerivativeCoefficient
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (by nlinarith [gaussianExpSecondDerivativeBaseBound_nonneg]))
  have hscale := secondSpatialDerivativeCoefficient_mul_sq_mul_sqrt ht
  have hscale' : ((4 * t)⁻¹) / 2 = (1 / 8 : ℝ) / t := by
    field_simp [ne_of_gt ht]
    ring
  rw [hscale']
  calc
    (√t + √s) ^ 5 *
        (secondSpatialDerivativeCoefficient t * exp (-((1 / 8 : ℝ) / t) * s)) =
        secondSpatialDerivativeCoefficient t *
          ((√t + √s) ^ 5 * exp (-((1 / 8 : ℝ) / t) * s)) := by ring
    _ ≤ secondSpatialDerivativeCoefficient t * (C₀ * t ^ 2 * √t) := by
      exact mul_le_mul_of_nonneg_left (hC t ht s hs) hcoeff
    _ = C₀ * secondSpatialDerivativeCoefficient 1 := by
      calc
        secondSpatialDerivativeCoefficient t * (C₀ * t ^ 2 * √t) =
            C₀ * (secondSpatialDerivativeCoefficient t * (t ^ 2 * √t)) := by ring
        _ = C₀ * secondSpatialDerivativeCoefficient 1 := by rw [hscale]

theorem summable_centered_spatial_majorant {b : ℝ} (hb : 0 < b)
    (y : Fin 3 → ℝ) :
    Summable (fun k : Fin 3 → ℤ => (∏ j,
      exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j))) := by
  let u : Fin 3 → ℤ → ℝ := fun j n =>
    exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b n
  have hu : ∀ j, Summable (u j) := by
    intro j
    exact (summable_gaussianOneDimMajorant hb).mul_left _
  have hnu : ∀ j n, 0 ≤ u j n := by
    intro j n
    exact mul_nonneg (exp_nonneg _) (gaussianOneDimMajorant_nonneg _)
  simpa [u] using summable_pi_fin3_prod_of hu hnu

theorem centered_spatial_majorant_prod_eq {b : ℝ} (y : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) :
    (∏ j, exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)) =
      exp (-b * sqNorm3 y) * ∏ j, gaussianOneDimMajorant b (k j) := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  unfold sqNorm3
  rw [← Finset.mul_sum]

theorem centered_spatial_majorant_tsum_eq {b : ℝ}
    (y : Fin 3 → ℝ) :
    (∑' k : Fin 3 → ℤ, ∏ j,
      exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)) =
      exp (-b * sqNorm3 y) *
        ∑' k : Fin 3 → ℤ, ∏ j, gaussianOneDimMajorant b (k j) := by
  calc
    _ = ∑' k : Fin 3 → ℤ, exp (-b * sqNorm3 y) *
        ∏ j, gaussianOneDimMajorant b (k j) := by
      apply tsum_congr
      intro k
      rw [centered_spatial_majorant_prod_eq]
    _ = _ := by rw [tsum_mul_left]

theorem heatKernelLift_first_spatial_deriv_term_le {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (k : Fin 3 → ℤ) :
    ‖iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)‖ ≤
      ((4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound)) *
        ∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
          gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) := by
  have h := gaussKernelSpaceLine_first_deriv_center_bound ht i y hy k
  simpa [norm_eq_abs, mul_assoc] using h

theorem heatKernelLift_first_spatial_deriv_majorant_summable {t : ℝ} (ht : 0 < t)
    (y : Fin 3 → ℝ) :
    Summable (fun k : Fin 3 → ℤ =>
      ((4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound)) *
        (∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
          gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)))) := by
  apply (summable_centered_spatial_majorant (by positivity) y).mul_left

theorem heatKernelLift_first_spatial_deriv_tsum_bound {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) (i : Fin 3) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |gaussKernelSpaceLine_first_deriv_tsum t i y| ≤
      firstSpatialDerivativeCoefficient t *
        exp (-firstSpatialDerivativeScale t * sqNorm3 y) *
          gaussianProductMajorantSum := by
  have hmaj := heatKernelLift_first_spatial_deriv_majorant_summable ht y
  have hbound := tsum_of_norm_bounded hmaj.hasSum
    (fun k => heatKernelLift_first_spatial_deriv_term_le ht i y hy k)
  unfold gaussKernelSpaceLine_first_deriv_tsum
  calc
    |∑' k : Fin 3 → ℤ,
        iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)| ≤
        ∑' k : Fin 3 → ℤ,
        ((4 * π * t) ^ (-(3 : ℝ) / 2) *
          (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound)) *
          ∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
            gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) :=
      hbound
    _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound) *
        (exp (-(((4 * t)⁻¹) / 2) * sqNorm3 y) *
          ∑' k : Fin 3 → ℤ, ∏ j,
            gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) := by
      rw [tsum_mul_left, centered_spatial_majorant_tsum_eq]
    _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * √(2 * ((4 * t)⁻¹)) * gaussianExpDerivativeBaseBound) *
        (exp (-(((4 * t)⁻¹) / 2) * sqNorm3 y) *
          gaussianProductMajorantSum) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (gaussianProductMajorant_tsum_le ht ht1)
          (exp_nonneg _))
      exact mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          gaussianExpDerivativeBaseBound_nonneg)
    _ = _ := by
      simp only [firstSpatialDerivativeCoefficient, firstSpatialDerivativeScale]
      ring_nf

theorem heatKernelLift_second_spatial_deriv_term_le {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (k : Fin 3 → ℤ) :
    ‖iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i)‖ ≤
      ((4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * ((4 * t)⁻¹) * (4 * gaussianExpSecondDerivativeBaseBound + 1))) *
        ∏ j, (exp (-(((4 * t)⁻¹) / 2) * (y j) ^ 2) *
          gaussianOneDimMajorant (((4 * t)⁻¹) / 2) (k j)) := by
  have h := gaussKernelSpaceLine_second_deriv_center_bound ht i y hy k
  simpa [norm_eq_abs, mul_assoc] using h

noncomputable def gaussKernelTimeDerivativeTsum (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℤ, ∑ i : Fin 3,
    iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i)

theorem heatKernelLift_time_deriv_tsum_bound {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |gaussKernelTimeDerivativeTsum t y| ≤
      3 * ((4 * π * t) ^ (-(3 : ℝ) / 2) *
        (2 * ((4 * t)⁻¹) * (4 * gaussianExpSecondDerivativeBaseBound + 1))) *
        exp (-(((4 * t)⁻¹) / 2) * sqNorm3 y) *
        gaussianProductMajorantSum := by
  let b : ℝ := ((4 * t)⁻¹) / 2
  let A : ℝ := (4 * π * t) ^ (-(3 : ℝ) / 2) *
    (2 * ((4 * t)⁻¹) * (4 * gaussianExpSecondDerivativeBaseBound + 1))
  have hcommon : Summable (fun k : Fin 3 → ℤ => A * ∏ j,
      exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)) := by
    apply (summable_centered_spatial_majorant (by dsimp [b]; positivity) y).mul_left
  have hcommon3 : Summable (fun k : Fin 3 → ℤ =>
      3 * (A * ∏ j, exp (-b * (y j) ^ 2) *
        gaussianOneDimMajorant b (k j))) := hcommon.mul_left 3
  have hterm : ∀ k : Fin 3 → ℤ, ‖∑ i : Fin 3,
      iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i)‖ ≤
        3 * (A * ∏ j, exp (-b * (y j) ^ 2) *
          gaussianOneDimMajorant b (k j)) := by
    intro k
    have h0 := heatKernelLift_second_spatial_deriv_term_le ht 0 y hy k
    have h1 := heatKernelLift_second_spatial_deriv_term_le ht 1 y hy k
    have h2 := heatKernelLift_second_spatial_deriv_term_le ht 2 y hy k
    have h0' : ‖iteratedDeriv 2 (gaussKernelSpaceLine t 0 y k) (y 0)‖ ≤
        A * ∏ j, exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j) := by
      simpa [A, b, mul_assoc] using h0
    have h1' : ‖iteratedDeriv 2 (gaussKernelSpaceLine t 1 y k) (y 1)‖ ≤
        A * ∏ j, exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j) := by
      simpa [A, b, mul_assoc] using h1
    have h2' : ‖iteratedDeriv 2 (gaussKernelSpaceLine t 2 y k) (y 2)‖ ≤
        A * ∏ j, exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j) := by
      simpa [A, b, mul_assoc] using h2
    simp only [Fin.sum_univ_three]
    calc
      ‖iteratedDeriv 2 (gaussKernelSpaceLine t 0 y k) (y 0) +
          iteratedDeriv 2 (gaussKernelSpaceLine t 1 y k) (y 1) +
            iteratedDeriv 2 (gaussKernelSpaceLine t 2 y k) (y 2)‖ ≤
          (‖iteratedDeriv 2 (gaussKernelSpaceLine t 0 y k) (y 0)‖ +
            ‖iteratedDeriv 2 (gaussKernelSpaceLine t 1 y k) (y 1)‖) +
              ‖iteratedDeriv 2 (gaussKernelSpaceLine t 2 y k) (y 2)‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ (A * ∏ j, exp (-b * (y j) ^ 2) *
          gaussianOneDimMajorant b (k j) +
            A * ∏ j, exp (-b * (y j) ^ 2) *
              gaussianOneDimMajorant b (k j)) +
          A * ∏ j, exp (-b * (y j) ^ 2) *
            gaussianOneDimMajorant b (k j) := by
        exact add_le_add (add_le_add h0' h1') h2'
      _ = _ := by ring
  have hbound := tsum_of_norm_bounded hcommon3.hasSum hterm
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (by nlinarith [gaussianExpSecondDerivativeBaseBound_nonneg]))
  unfold gaussKernelTimeDerivativeTsum
  calc
    |∑' k : Fin 3 → ℤ, ∑ i : Fin 3,
        iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i)| ≤
        ∑' k : Fin 3 → ℤ, 3 * (A * ∏ j,
          exp (-b * (y j) ^ 2) * gaussianOneDimMajorant b (k j)) := hbound
    _ = 3 * (A * (exp (-b * sqNorm3 y) *
        ∑' k : Fin 3 → ℤ, ∏ j, gaussianOneDimMajorant b (k j))) := by
      rw [tsum_mul_left, tsum_mul_left, centered_spatial_majorant_tsum_eq]
    _ ≤ 3 * (A * (exp (-b * sqNorm3 y) * gaussianProductMajorantSum)) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (gaussianProductMajorant_tsum_le ht ht1)
            (exp_nonneg _)) hA)
      norm_num
    _ = _ := by
      simp only [A, b]
      ring

end RegularityStructures

end
