/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelRegularity
public import RegularityStructures.Torus.KernelBoundsBasic

/-!
# Gaussian majorants for the torus heat kernel

The one-dimensional majorant from `HeatKernelRegularity` can be fixed at the scale `t = 1`. This
gives a summable, `t`-independent lattice majorant for `0 < t ≤ 1`, and hence the first
time-singular estimate needed for the torus kernel bounds.  The constants in this file are
introduced before any point variable; this is the convention used by Hairer's kernel estimates.

Source: [Hai14, Assumption 5.1 and (5.4)].
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem gaussianOneDimMajorant_mono {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (n : ℤ) :
    gaussianOneDimMajorant ((4 * t)⁻¹) n ≤ gaussianOneDimMajorant (1 / 4) n := by
  have hinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1
  have hcoef : (1 / 4 / 4 : ℝ) ≤ ((4 * t)⁻¹) / 4 := by
    calc
      (1 / 4 / 4 : ℝ) = (1 / 16 : ℝ) * 1 := by norm_num
      _ ≤ (1 / 16 : ℝ) * t⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = ((4 * t)⁻¹) / 4 := by field_simp; norm_num
  have hexp : exp (-((4 * t)⁻¹ / 4) * (n : ℝ) ^ 2) ≤
      exp (-(1 / 4 / 4 : ℝ) * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ)]
  unfold gaussianOneDimMajorant
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · simp only [hn, ↓reduceIte]
    simpa [add_comm] using add_le_add_left hexp 1
  · simp only [hn, ↓reduceIte, zero_add]
    exact hexp

noncomputable def heatKernelMajorant : ℝ :=
  ∑' k : Fin 3 → ℤ, ∏ i, gaussianOneDimMajorant (1 / 4) (k i)

theorem summable_heatKernelMajorant :
    Summable (fun k : Fin 3 → ℤ => ∏ i, gaussianOneDimMajorant (1 / 4) (k i)) := by
  exact summable_pi_fin3_prod
    (summable_gaussianOneDimMajorant (by norm_num)) gaussianOneDimMajorant_nonneg

theorem nonneg_heatKernelMajorant : 0 ≤ heatKernelMajorant := by
  unfold heatKernelMajorant
  exact tsum_nonneg fun k => Finset.prod_nonneg fun i _ => gaussianOneDimMajorant_nonneg _

theorem sq_centered_add_int_ge {y : ℝ} (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (n : ℤ) : y ^ 2 ≤ (y + (n : ℝ)) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · have hnle : (n : ℝ) ≤ -1 := by
      have h : (1 : ℝ) ≤ ((-n : ℤ) : ℝ) :=
        Int.cast_one_le_of_pos (show (0 : ℤ) < -n by omega)
      norm_num at h
      linarith
    have hright : 0 ≤ -(y + (n : ℝ)) := by linarith [hy.2]
    have habs : |y| ≤ -(y + (n : ℝ)) := by
      rw [abs_le]
      constructor <;> nlinarith [hy.1, hy.2]
    have hsq := (sq_le_sq₀ (abs_nonneg y) hright).2 habs
    calc
      y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      _ ≤ (-(y + (n : ℝ))) ^ 2 := hsq
      _ = (y + (n : ℝ)) ^ 2 := by rw [neg_sq]
  · have hnle : (1 : ℝ) ≤ (n : ℝ) := Int.cast_one_le_of_pos hnpos
    have hright : 0 ≤ y + (n : ℝ) := by linarith [hy.1]
    have habs : |y| ≤ y + (n : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [hy.1, hy.2]
    have hsq := (sq_le_sq₀ (abs_nonneg y) hright).2 habs
    simpa only [sq_abs] using hsq

theorem sq_centered_add_int_tail_ge {y : ℝ}
    (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) {n : ℤ}
    (hn : n ∉ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)) :
    y ^ 2 + (n : ℝ) ^ 2 / 2 ≤ (y + (n : ℝ)) ^ 2 := by
  have hnlarge : n ≤ -2 ∨ 2 ≤ n := by
    have hn' : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or, not_false_eq_true] using hn
    omega
  rcases hnlarge with hnlarge | hnlarge
  · have hnreal : (n : ℝ) ≤ -2 := by exact_mod_cast hnlarge
    have hprod : 0 ≤ (-((n : ℝ))) * (-((n : ℝ)) - 2) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hy.2, hprod]
  · have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
    have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hy.1, hprod]

theorem gaussian_shift_exp_le {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) (n : ℤ) :
    exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤
      exp (-y ^ 2 / (4 * t)) * gaussianOneDimMajorant (1 / 4) n := by
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · have hsq := sq_centered_add_int_ge hy n
    have hbase : exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤ exp (-y ^ 2 / (4 * t)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hsq]
    rw [gaussianOneDimMajorant]
    simp only [hn, ↓reduceIte]
    exact hbase.trans (le_mul_of_one_le_right (exp_nonneg _) (by
      linarith [exp_nonneg (-(1 / 4 / 4 : ℝ) * (n : ℝ) ^ 2)]))
  · have hsq := sq_centered_add_int_tail_ge hy hn
    have hcoeff : (n : ℝ) ^ 2 / 16 ≤ (n : ℝ) ^ 2 / (8 * t) := by
      have hnt : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      have hden : 0 < 8 * t := by positivity
      apply (div_le_div_iff₀ (by norm_num) hden).2
      nlinarith [ht1, hnt]
    have hexp : -((y + (n : ℝ)) ^ 2) / (4 * t) ≤
        -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / 16 := by
      have hnum : -((y + (n : ℝ)) ^ 2) ≤
          -y ^ 2 - (n : ℝ) ^ 2 / 16 * (4 * t) := by
        have hterm : (n : ℝ) ^ 2 / 16 * (4 * t) ≤ (n : ℝ) ^ 2 / 2 := by
          nlinarith [ht1, sq_nonneg (n : ℝ)]
        nlinarith [hsq, hterm]
      calc
        -((y + (n : ℝ)) ^ 2) / (4 * t) ≤
            (-y ^ 2 - (n : ℝ) ^ 2 / 16 * (4 * t)) / (4 * t) :=
          (div_le_div_iff₀ (by positivity) (by positivity)).2
            (mul_le_mul_of_nonneg_right hnum (by positivity))
        _ = -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / 16 := by field_simp
    rw [gaussianOneDimMajorant]
    simp only [hn, ↓reduceIte, zero_add]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert hexp using 1
    ring

theorem torusRep_eq_centered_add_int (x : Torus3) :
    ∃ m : Fin 3 → ℤ, torusRep x = torusCenteredRep x + fun i => (m i : ℝ) := by
  let m : Fin 3 → ℤ := fun i => if (1 / 2 : ℝ) ≤ torusRep x i then 1 else 0
  refine ⟨m, ?_⟩
  funext i
  dsimp [m, torusCenteredRep]
  split_ifs <;> ring

theorem heatKernel_eq_centered_lift (t : ℝ) (x : Torus3) :
    heatKernel t x = heatKernelLift t (torusCenteredRep x) := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  calc
    heatKernel t x = heatKernelLift t (torusRep x) := by rfl
    _ = heatKernelLift t (torusCenteredRep x) := by rw [hm, heatKernelLift_add_integer]

theorem heatKernel_le_spatial_gaussian {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : Torus3) :
    heatKernel t x ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-sqNorm3 (torusCenteredRep x) / (4 * t)) * heatKernelMajorant := by
  let y : Fin 3 → ℝ := torusCenteredRep x
  have hA : Summable (fun k : Fin 3 → ℤ =>
      ∏ i, gaussianOneDimMajorant (1 / 4) (k i)) := summable_heatKernelMajorant
  have hy : ∀ i, y i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    intro i
    exact torusCenteredRep_mem_Icc x i
  have hterm : ∀ k : Fin 3 → ℤ,
      gaussKernel t (y + fun i => (k i : ℝ)) ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          exp (-sqNorm3 y / (4 * t)) *
            ∏ i, gaussianOneDimMajorant (1 / 4) (k i) := by
    intro k
    rw [gaussKernel_eq_prod]
    have hprod :
        (∏ i, exp (-((y i) ^ 2) / (4 * t)) *
            gaussianOneDimMajorant (1 / 4) (k i)) =
          exp (-sqNorm3 y / (4 * t)) *
            ∏ i, gaussianOneDimMajorant (1 / 4) (k i) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      unfold sqNorm3
      rw [← Finset.sum_div]
      simp
    have hexpform : ∀ i : Fin 3,
        exp (-(4 * t)⁻¹ * (y i + (k i : ℝ)) ^ 2) =
          exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t)) := by
      intro i
      congr 1
      ring
    simp_rw [Pi.add_apply, hexpform]
    have hprod_le :
        (∏ i, exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t))) ≤
          ∏ i, exp (-y i ^ 2 / (4 * t)) *
            gaussianOneDimMajorant (1 / 4) (k i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact exp_nonneg _
      · intro i hi
        exact gaussian_shift_exp_le ht ht1 (hy i) (k i)
    calc
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t)) ≤
          (4 * π * t) ^ (-(3 : ℝ) / 2) *
            ∏ i, exp (-y i ^ 2 / (4 * t)) *
              gaussianOneDimMajorant (1 / 4) (k i) :=
        mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          exp (-sqNorm3 y / (4 * t)) *
            ∏ i, gaussianOneDimMajorant (1 / 4) (k i) := by
        rw [hprod]
        ring
  have hgauss : Summable (fun k : Fin 3 → ℤ =>
      gaussKernel t (y + fun i => (k i : ℝ))) := by
    apply (summable_gaussian_vector_majorant ht).of_nonneg_of_le
    · intro k
      exact gaussKernel_nonneg ht _
    · intro k
      have hbound := gaussKernel_le_uniform_majorant (y := y) ht
        (fun i => ⟨(show (-1 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num).trans (hy i).1,
          (hy i).2.trans (by norm_num : (1 / 2 : ℝ) ≤ 2)⟩) k
      rw [Real.norm_of_nonneg (gaussKernel_nonneg ht _)] at hbound
      exact hbound
  have hright : Summable (fun k : Fin 3 → ℤ =>
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-sqNorm3 y / (4 * t)) *
          ∏ i, gaussianOneDimMajorant (1 / 4) (k i)) := by
    exact hA.mul_left _
  have hsum := hgauss.tsum_le_tsum hterm hright
  rw [heatKernel_eq_centered_lift, heatKernelLift]
  calc
    (∑' k : Fin 3 → ℤ, gaussKernel t (y + fun i => (k i : ℝ))) ≤
        ∑' k : Fin 3 → ℤ,
          (4 * π * t) ^ (-(3 : ℝ) / 2) *
            exp (-sqNorm3 y / (4 * t)) *
              ∏ i, gaussianOneDimMajorant (1 / 4) (k i) := hsum
    _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          exp (-sqNorm3 y / (4 * t)) * heatKernelMajorant := by
      rw [show heatKernelMajorant =
          ∑' k : Fin 3 → ℤ, ∏ i, gaussianOneDimMajorant (1 / 4) (k i) by rfl]
      exact hA.tsum_mul_left _

theorem exp_neg_sq_div_four_mul_one_add_cube_le {u : ℝ} (hu : 0 ≤ u) :
    exp (-u ^ 2 / 4) * (1 + u) ^ 3 ≤ 512 := by
  by_cases hu1 : u ≤ 1
  · have hpoly : (1 + u) ^ 3 ≤ (2 : ℝ) ^ 3 := by
      gcongr
      linarith
    have hexp : exp (-u ^ 2 / 4) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg u]
    calc
      exp (-u ^ 2 / 4) * (1 + u) ^ 3 ≤ (1 : ℝ) * (1 + u) ^ 3 :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ 512 := by nlinarith [hpoly]
  · have hu1' : 1 ≤ u := le_of_not_gt (fun h => hu1 h.le)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1'
    let v : ℝ := u ^ 2 / 4
    have hv : 0 < v := by
      dsimp [v]
      positivity
    have hvhalf : v / 2 ≤ exp (v / 2) := by
      have h := Real.add_one_le_exp (v / 2)
      nlinarith
    have hsquare : v ^ 2 / 4 ≤ exp v := by
      calc
        v ^ 2 / 4 ≤ (exp (v / 2)) ^ 2 := by
          have hs := (sq_le_sq₀ (show 0 ≤ v / 2 by positivity)
            (show 0 ≤ exp (v / 2) by positivity)).2 hvhalf
          nlinarith [hs]
        _ = exp v := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    have hu4 : 0 < u ^ 4 := by positivity
    have hexp : exp (-u ^ 2 / 4) ≤ 64 / u ^ 4 := by
      have hvbound : u ^ 4 / 64 ≤ exp v := by
        convert hsquare using 1
        dsimp [v]
        ring
      apply (le_div_iff₀ hu4).2
      rw [show -u ^ 2 / 4 = -v by dsimp [v]; ring, Real.exp_neg]
      apply (inv_mul_le_iff₀ (exp_pos v)).2
      nlinarith [hvbound]
    have hpoly : (1 + u) ^ 3 ≤ (2 * u) ^ 3 := by
      gcongr
      linarith
    calc
      exp (-u ^ 2 / 4) * (1 + u) ^ 3 ≤
          (64 / u ^ 4) * (1 + u) ^ 3 :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ (64 / u ^ 4) * (2 * u) ^ 3 :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 512 / u := by field_simp; norm_num
      _ ≤ 512 := by
        apply (div_le_iff₀ hu0).2
        nlinarith

theorem massiveHeatKernel_singular_bound :
    ∃ C : ℝ, ∀ z : SpaceTime, 0 < torusParabolicSize z →
      torusParabolicSize z ≤ 1 →
        0 ≤ massiveHeatKernel z ∧
          massiveHeatKernel z ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) := by
  let A : ℝ := heatKernelMajorant
  let B : ℝ := (4 * π) ^ (-(3 : ℝ) / 2) * A
  let C : ℝ := 512 * B
  have hA : 0 ≤ A := by
    exact nonneg_heatKernelMajorant
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) hA
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, ?_⟩
  intro z hz hz1
  have hq : 0 ≤ torusParabolicSize z := torusParabolicSize_nonneg z
  constructor
  · exact massiveHeatKernel_nonneg z
  by_cases ht : z.1 ≤ 0
  · rw [massiveHeatKernel, ite_eq_right (not_lt.mpr ht)]
    exact mul_nonneg hC (Real.rpow_nonneg hq _)
  · have htpos : 0 < z.1 := lt_of_not_ge ht
    let s : ℝ := √z.1
    let d : ℝ := torusSpatialNorm z.2
    let u : ℝ := d / s
    have hs : 0 < s := by
      dsimp [s]
      positivity
    have hd : 0 ≤ d := torusSpatialNorm_nonneg z.2
    have hu : 0 ≤ u := by
      dsimp [u]
      exact div_nonneg hd hs.le
    have hs_sq : s ^ 2 = z.1 := by
      dsimp [s]
      exact Real.sq_sqrt htpos.le
    have ht1 : z.1 ≤ 1 := by
      have hs_le : s ≤ 1 := by
        have hst : s ≤ torusParabolicSize z := by
          rw [torusParabolicSize, abs_of_pos htpos]
          dsimp [s]
          linarith [torusSpatialNorm_nonneg z.2]
        linarith
      nlinarith [hs_sq]
    have hsp := heatKernel_le_spatial_gaussian htpos ht1 z.2
    have hE : exp (-u ^ 2 / 4) ≤ 512 * (1 + u) ^ (-(3 : ℝ)) := by
      have hpoly := exp_neg_sq_div_four_mul_one_add_cube_le hu
      have hden : 0 < (1 + u) ^ (3 : ℕ) := by positivity
      have hdiv : exp (-u ^ 2 / 4) ≤ 512 / (1 + u) ^ (3 : ℕ) := by
        exact (le_div_iff₀ hden).2 hpoly
      calc
        exp (-u ^ 2 / 4) ≤ 512 / (1 + u) ^ (3 : ℕ) := hdiv
        _ = 512 * (1 + u) ^ (-(3 : ℝ)) := by
          rw [Real.rpow_neg (by positivity)]
          simp [div_eq_mul_inv]
    have hsq_d : d ^ 2 = sqNorm3 (torusCenteredRep z.2) := by
      exact torusSpatialNorm_sq z.2
    have hEform : exp (-sqNorm3 (torusCenteredRep z.2) / (4 * z.1)) =
        exp (-u ^ 2 / 4) := by
      congr 1
      dsimp [u, d, s]
      rw [← hsq_d]
      field_simp [ne_of_gt hs]
      dsimp [d]
      rw [Real.sq_sqrt htpos.le]
      ring
    have hqform : torusParabolicSize z = s * (1 + u) := by
      rw [torusParabolicSize, abs_of_pos htpos]
      dsimp [s, d, u]
      field_simp [ne_of_gt hs]
    have ht_rpow : z.1 ^ (-(3 : ℝ) / 2) = s ^ (-(3 : ℝ)) := by
      rw [← hs_sq, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hpref :
        (4 * π * z.1) ^ (-(3 : ℝ) / 2) =
          (4 * π) ^ (-(3 : ℝ) / 2) * s ^ (-(3 : ℝ)) := by
      rw [show 4 * π * z.1 = (4 * π) * z.1 by ring,
        Real.mul_rpow (by positivity) htpos.le, ht_rpow]
    have hq_rpow : torusParabolicSize z ^ (-(3 : ℝ)) =
        s ^ (-(3 : ℝ)) * (1 + u) ^ (-(3 : ℝ)) := by
      rw [hqform, Real.mul_rpow hs.le (by positivity)]
    have hG : massiveHeatKernel z ≤
        (4 * π * z.1) ^ (-(3 : ℝ) / 2) *
          exp (-sqNorm3 (torusCenteredRep z.2) / (4 * z.1)) * A := by
      calc
        massiveHeatKernel z = exp (-z.1) * heatKernel z.1 z.2 := by
          simp [massiveHeatKernel, htpos]
        _ ≤ heatKernel z.1 z.2 := by
          have hexp : exp (-z.1) ≤ (1 : ℝ) := by
            rw [Real.exp_le_one_iff]
            linarith
          simpa [mul_comm] using
            mul_le_of_le_one_right (heatKernel_nonneg htpos z.2) hexp
        _ ≤ _ := hsp
    have hG' : massiveHeatKernel z ≤
        B * s ^ (-(3 : ℝ)) * exp (-u ^ 2 / 4) := by
      calc
        massiveHeatKernel z ≤
            (4 * π * z.1) ^ (-(3 : ℝ) / 2) *
              exp (-sqNorm3 (torusCenteredRep z.2) / (4 * z.1)) * A := hG
        _ = B * s ^ (-(3 : ℝ)) * exp (-u ^ 2 / 4) := by
          dsimp [B]
          rw [hEform, hpref]
          ring
    calc
      massiveHeatKernel z ≤ B * s ^ (-(3 : ℝ)) *
          (512 * (1 + u) ^ (-(3 : ℝ))) := by
        exact hG'.trans (mul_le_mul_of_nonneg_left hE
          (mul_nonneg hB (Real.rpow_nonneg hs.le _)))
      _ = C * torusParabolicSize z ^ (-(3 : ℝ)) := by
        dsimp [C]
        rw [hq_rpow]
        ring

theorem heatKernel_le_time_singular :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : Torus3,
      heatKernel t x ≤ C * t ^ (-(3 : ℝ) / 2) := by
  let A : ℝ := heatKernelMajorant
  let C : ℝ := (4 * π) ^ (-(3 : ℝ) / 2) * A
  have hA : Summable (fun k : Fin 3 → ℤ =>
      ∏ i, gaussianOneDimMajorant (1 / 4) (k i)) := summable_heatKernelMajorant
  have hAt : ∀ {t : ℝ}, 0 < t → Summable (fun k : Fin 3 → ℤ =>
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) := by
    intro t ht
    exact summable_gaussian_vector_majorant ht
  refine ⟨C, ?_⟩
  intro t ht x
  have htpos : 0 < t := ht.1
  have htmajor := heatKernel_le_uniform_majorant htpos x
  have hpoint : ∀ k : Fin 3 → ℤ,
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant (1 / 4) (k i) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.prod_le_prod₀
    · intro i hi
      exact gaussianOneDimMajorant_nonneg _
    · intro i hi
      exact gaussianOneDimMajorant_mono htpos ht.2 (k i)
  have hsum : Summable (fun k : Fin 3 → ℤ =>
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant (1 / 4) (k i)) := hA.mul_left _
  calc
    heatKernel t x ≤ ∑' k : Fin 3 → ℤ,
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) := htmajor
    _ ≤ ∑' k : Fin 3 → ℤ,
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant (1 / 4) (k i) :=
      (hAt htpos).tsum_le_tsum hpoint hsum
    _ = (4 * π * t) ^ (-(3 : ℝ) / 2) * A := by
      rw [show A = ∑' k : Fin 3 → ℤ, ∏ i, gaussianOneDimMajorant (1 / 4) (k i) by
        rfl]
      exact hA.tsum_mul_left _
    _ = C * t ^ (-(3 : ℝ) / 2) := by
      dsimp [C]
      rw [show 4 * π * t = (4 * π) * t by ring,
        Real.mul_rpow (by positivity) (by positivity)]
      ring

end RegularityStructures

end
