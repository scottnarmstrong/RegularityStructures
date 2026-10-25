/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Large-time bounds for the massive torus heat kernel

The periodised Gaussian has a uniformly bounded spatial profile once `t ≥ 1`.  The proof uses
the one-dimensional Jacobi transformation, followed by factorisation over the three coordinates.
This is the large-scale part of [Hai14, Assumption 5.1, (5.3)] (arXiv:1303.5113v4).
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures

private def fin3ProdEquiv : ((ℤ × ℤ) × ℤ) ≃ (Fin 3 → ℤ) :=
  ((Equiv.prodAssoc ℤ ℤ ℤ).trans
    (Equiv.prodCongr (Equiv.refl ℤ)
      ((piFinTwoEquiv (fun _ : Fin 2 => ℤ)).symm))).trans
    (Fin.consEquiv (fun _ : Fin 3 => ℤ))

private theorem fin3_prod_equiv_apply (p : (ℤ × ℤ) × ℤ) (f : ℤ → ℝ) :
    ∏ i, f (fin3ProdEquiv p i) = (f p.1.1 * f p.1.2) * f p.2 := by
  simp [fin3ProdEquiv, Fin.prod_univ_succ, piFinTwoEquiv]
  ring

theorem tsum_fin3_prod_eq_cube {f : ℤ → ℝ} (hf : Summable f)
    (hf0 : ∀ n, 0 ≤ f n) :
    (∑' k : Fin 3 → ℤ, ∏ i, f (k i)) = (∑' n : ℤ, f n) ^ 3 := by
  let e := fin3ProdEquiv
  have hprod : Summable (fun p : (ℤ × ℤ) × ℤ =>
      (f p.1.1 * f p.1.2) * f p.2) := by
    have h12 : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) :=
      hf.mul_of_nonneg hf (fun _ => hf0 _) (fun _ => hf0 _)
    exact h12.mul_of_nonneg hf
      (fun p => mul_nonneg (hf0 p.1) (hf0 p.2)) (fun _ => hf0 _)
  calc
    (∑' k : Fin 3 → ℤ, ∏ i, f (k i)) =
        ∑' p : (ℤ × ℤ) × ℤ, ∏ i, f (e p i) := by
      symm
      simpa [e] using (e.tsum_eq (fun k : Fin 3 → ℤ => ∏ i, f (k i)))
    _ = ∑' p : (ℤ × ℤ) × ℤ, (f p.1.1 * f p.1.2) * f p.2 := by
      apply tsum_congr
      intro p
      simpa [e] using fin3_prod_equiv_apply p f
    _ = ∑' p : ℤ × ℤ, ∑' n : ℤ, (f p.1 * f p.2) * f n :=
      by
        simpa [Prod.fst, Prod.snd, mul_assoc] using
          hprod.tsum_prod' (fun p => hf.mul_left (f p.1 * f p.2))
    _ = (∑' p : ℤ × ℤ, f p.1 * f p.2) * (∑' n : ℤ, f n) := by
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ = (∑' n : ℤ, f n) ^ 3 := by
      have h12 : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) :=
        hf.mul_of_nonneg hf (fun _ => hf0 _) (fun _ => hf0 _)
      have hp : (∑' p : ℤ × ℤ, f p.1 * f p.2) = (∑' n : ℤ, f n) ^ 2 := by
        calc
          (∑' p : ℤ × ℤ, f p.1 * f p.2) =
              ∑' b : ℤ, ∑' c : ℤ, f b * f c := by
            simpa only [Prod.fst, Prod.snd] using
              h12.tsum_prod' (fun b => hf.mul_left (f b))
          _ = ∑' b : ℤ, f b * (∑' c : ℤ, f c) := by
            simp_rw [tsum_mul_left]
          _ = (∑' n : ℤ, f n) ^ 2 := by
            rw [tsum_mul_right]
            ring
      rw [hp]
      ring

private def thetaDual : ℝ := ∑' n : ℤ, exp (-(16 * π ^ 2) * (n : ℝ) ^ 2)

private theorem summable_thetaDual : Summable (fun n : ℤ =>
    exp (-(16 * π ^ 2) * (n : ℝ) ^ 2)) := by
  have h := summable_exp_neg_mul_sq_int (by positivity : 0 < (16 * π ^ 2 : ℝ))
    (by simp : (0 : ℝ) ∈ Set.Ico 0 1)
  convert h using 1
  funext n
  congr 2
  ring

private theorem thetaDual_nonneg : 0 ≤ thetaDual := by
  dsimp [thetaDual]
  exact tsum_nonneg (fun n => exp_nonneg _)

private theorem theta_one_dim_bound {t : ℝ} (ht : 1 ≤ t) :
    (∑' n : ℤ, gaussianOneDimMajorant ((4 * t)⁻¹) n) ≤
      (6 + 4 * √π * thetaDual) * √t := by
  let a : ℝ := (16 * π * t)⁻¹
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have htheta := Real.tsum_exp_neg_mul_int_sq ha
  have hsum : Summable (fun n : ℤ =>
      exp (-(π * a) * (n : ℝ) ^ 2)) := by
    simpa using (summable_exp_neg_mul_sq_int (a := π * a) (b := 0) (by positivity)
      (by simp : (0 : ℝ) ∈ Set.Ico 0 1))
  have hscaled : (∑' n : ℤ, exp (-(n : ℝ) ^ 2 / (16 * t))) =
      √(16 * π * t) *
        (∑' n : ℤ, exp (-(16 * π ^ 2 * t) * (n : ℝ) ^ 2)) := by
    calc
      (∑' n : ℤ, exp (-(n : ℝ) ^ 2 / (16 * t))) =
          ∑' n : ℤ, exp (-(π * a) * (n : ℝ) ^ 2) := by
            apply tsum_congr
            intro n
            congr 2
            dsimp [a]
            field_simp
      _ = (1 / a ^ (1 / 2 : ℝ)) *
          (∑' n : ℤ, exp (-(π / a) * (n : ℝ) ^ 2)) := by
            convert htheta using 1 <;> simp [div_eq_mul_inv]
      _ = √(16 * π * t) *
          (∑' n : ℤ, exp (-(16 * π ^ 2 * t) * (n : ℝ) ^ 2)) := by
        dsimp [a, thetaDual]
        have hroot : 1 / (16 * π * t)⁻¹ ^ (1 / 2 : ℝ) = √(16 * π * t) := by
          rw [Real.inv_rpow (by positivity : 0 ≤ (16 * π * t : ℝ))]
          simp [Real.sqrt_eq_rpow]
        rw [hroot]
        congr 1
        apply tsum_congr
        intro n
        congr 2
        field_simp
  have hdual : (∑' n : ℤ, exp (-(16 * π ^ 2 * t) * (n : ℝ) ^ 2)) ≤ thetaDual := by
    have hleft : Summable (fun n : ℤ => exp (-(16 * π ^ 2 * t) * (n : ℝ) ^ 2)) := by
      simpa using (summable_exp_neg_mul_sq_int (a := 16 * π ^ 2 * t) (b := 0)
        (by positivity) (by simp : (0 : ℝ) ∈ Set.Ico 0 1))
    apply hleft.tsum_le_tsum
    · intro n
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      have hcoef : 16 * π ^ 2 ≤ 16 * π ^ 2 * t := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ (16 * π ^ 2 : ℝ))
      nlinarith
    · exact summable_thetaDual
  have hmajor : (∑' n : ℤ, gaussianOneDimMajorant ((4 * t)⁻¹) n) =
      6 + ∑' n : ℤ, exp (-(n : ℝ) ^ 2 / (16 * t)) := by
    unfold gaussianOneDimMajorant
    have hsum₁ : Summable (fun n : ℤ =>
        if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (1 : ℝ) else 0) := by
      apply summable_of_ne_finset_zero (s := {-3, -2, -1, 0, 1, 2})
      intro n hn
      simp [hn]
    have hsum₂ : Summable (fun n : ℤ =>
        exp (-((4 * t)⁻¹ / 4) * (n : ℝ) ^ 2)) := by
      have ha : 0 < (4 * t)⁻¹ / 4 := by positivity
      have hraw := summable_exp_neg_mul_sq_int (a := (4 * t)⁻¹ / 4) (b := 0) ha
        (by simp : (0 : ℝ) ∈ Set.Ico 0 1)
      simpa only [zero_add] using hraw
    calc
      (∑' n : ℤ, ((if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (1 : ℝ) else 0) +
          exp (-((4 * t)⁻¹ / 4) * (n : ℝ) ^ 2))) =
      (∑' n : ℤ, if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (1 : ℝ) else 0) +
            ∑' n : ℤ, exp (-((4 * t)⁻¹ / 4) * (n : ℝ) ^ 2) :=
        hsum₁.tsum_add hsum₂
      _ = 6 + ∑' n : ℤ, exp (-(n : ℝ) ^ 2 / (16 * t)) := by
        have hfinite : (∑' n : ℤ,
            if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (1 : ℝ) else 0) = 6 := by
          rw [tsum_eq_sum (s := ({-3, -2, -1, 0, 1, 2} : Finset ℤ))]
          · calc
              (∑ x ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ),
                  if x ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (1 : ℝ) else 0) =
                  ∑ x ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ), (1 : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    simp [hx]
              _ = 6 := by
                rw [Finset.sum_const]
                norm_num [Finset.card_insert_of_notMem]
          · intro n hn
            simp [hn]
        rw [hfinite]
        congr 1
        apply tsum_congr
        intro n
        congr 1
        ring
  rw [hmajor, hscaled]
  have hsqrt : √(16 * π * t) = 4 * √π * √t := by
    rw [show 16 * π * t = 16 * (π * t) by ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (16 : ℝ)),
      Real.sqrt_mul (by positivity : 0 ≤ π)]
    have h16 : √(16 : ℝ) = 4 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16)
      nlinarith [Real.sqrt_nonneg (16 : ℝ)]
    rw [h16]
    ring
  have hroot : 1 ≤ √t := by
    have hs := Real.sqrt_le_sqrt ht
    simpa using hs
  calc
    6 + √(16 * π * t) *
        (∑' n : ℤ, exp (-(16 * π ^ 2 * t) * (n : ℝ) ^ 2)) ≤
        6 + √(16 * π * t) * thetaDual := by
          gcongr
    _ = 6 + 4 * √π * thetaDual * √t := by rw [hsqrt]; ring
    _ ≤ (6 + 4 * √π * thetaDual) * √t := by
      have h6 : 6 ≤ 6 * √t := by nlinarith
      nlinarith [thetaDual_nonneg, Real.sqrt_nonneg π]

theorem heatKernel_le_large_time :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ x : Torus3, heatKernel t x ≤ C := by
  let D : ℝ := 6 + 4 * √π * thetaDual
  have hD : 0 ≤ D := by
    dsimp [D]
    have hπ : 0 ≤ (π : ℝ) := Real.pi_pos.le
    have hs : 0 ≤ √π := Real.sqrt_nonneg _
    nlinarith [thetaDual_nonneg]
  let C : ℝ := (4 * π) ^ (-(3 : ℝ) / 2) * D ^ 3
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, ?_⟩
  intro t ht x
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hmaj := heatKernel_le_uniform_majorant htpos x
  have hsum := theta_one_dim_bound ht
  have hfactor : (∑' k : Fin 3 → ℤ,
      ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) ≤ D ^ 3 * t ^ (3 / 2 : ℝ) := by
    rw [tsum_fin3_prod_eq_cube]
    · dsimp [D]
      have hnon : 0 ≤ ∑' n : ℤ, gaussianOneDimMajorant ((4 * t)⁻¹) n :=
        tsum_nonneg (fun n => gaussianOneDimMajorant_nonneg _)
      have hp := pow_le_pow_left₀ hnon hsum (3 : ℕ)
      have hsquare : (√t) ^ 2 = t := Real.sq_sqrt (le_trans zero_le_one ht)
      have hsqrtpow : (√t) ^ 3 = t ^ (3 / 2 : ℝ) := by
        have htr : t ^ (3 / 2 : ℝ) = t * √t := by
          rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring,
            Real.rpow_add htpos, Real.rpow_one, Real.sqrt_eq_rpow]
        rw [show (√t) ^ 3 = (√t) ^ 2 * √t by ring, hsquare, htr]
      calc
        (∑' n : ℤ, gaussianOneDimMajorant ((4 * t)⁻¹) n) ^ 3 ≤
            ((6 + 4 * √π * thetaDual) * √t) ^ 3 := hp
        _ = (6 + 4 * √π * thetaDual) ^ 3 * t ^ (3 / 2 : ℝ) := by
          rw [mul_pow, hsqrtpow]
    · exact summable_gaussianOneDimMajorant (by positivity)
    · intro n
      exact gaussianOneDimMajorant_nonneg _
  have hprefeq : (4 * π * t) ^ (-(3 : ℝ) / 2) =
      (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
    rw [show 4 * π * t = (4 * π) * t by ring,
      Real.mul_rpow (by positivity) htpos.le]
  calc
    heatKernel t x ≤ ∑' k : Fin 3 → ℤ,
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) := hmaj
    _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
        (∑' k : Fin 3 → ℤ,
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) := by
      rw [tsum_mul_left]
    _ = (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) *
        (∑' k : Fin 3 → ℤ,
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) := by
      rw [hprefeq]
    _ ≤ (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) *
        (D ^ 3 * t ^ (3 / 2 : ℝ)) := by
      have hsum0 : 0 ≤ ∑' k : Fin 3 → ℤ,
          ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) :=
        tsum_nonneg (fun k => Finset.prod_nonneg fun i _ => gaussianOneDimMajorant_nonneg _)
      exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = C := by
      dsimp [C]
      have hcancel : t ^ (-(3 : ℝ) / 2) * t ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add htpos]
        norm_num
      calc
        (4 * π) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) *
            (D ^ 3 * t ^ (3 / 2 : ℝ)) =
            (4 * π) ^ (-(3 : ℝ) / 2) * D ^ 3 *
              (t ^ (-(3 : ℝ) / 2) * t ^ (3 / 2 : ℝ)) := by ring
        _ = (4 * π) ^ (-(3 : ℝ) / 2) * D ^ 3 := by rw [hcancel, mul_one]

theorem massiveHeatKernel_exponential_bound :
    ∃ C : ℝ, ∀ z : SpaceTime, 1 ≤ z.1 →
      massiveHeatKernel z ≤ C * exp (-z.1) := by
  rcases heatKernel_le_large_time with ⟨C₀, hC₀⟩
  refine ⟨C₀, ?_⟩
  intro z ht
  have htpos : 0 < z.1 := lt_of_lt_of_le (by norm_num) ht
  simp only [massiveHeatKernel, htpos, ite_true]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right (hC₀ z.1 ht z.2) (exp_nonneg (-z.1))

end RegularityStructures

end
