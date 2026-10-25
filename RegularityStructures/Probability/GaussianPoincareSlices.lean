/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincareFinite

/-!
# Derivatives of the remaining-coordinate Gaussian slices

The induction removes the first coordinate.  This file packages the continuous-linear derivative
of the resulting affine insertion map and its norm bound.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

def finConsRestLinearMap (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
    if hi : i = 0 then 0 else
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (i.pred hi)))

lemma contDiff_fin_cons_scalar {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => finCons x y) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    have hfun : (fun x : ℝ => finCons x y 0) = id := by
      funext x
      simp [finCons]
    rw [hfun]
    exact contDiff_id
  · have hfun : (fun x : ℝ => finCons x y i) = fun _ => y (i.pred hi) := by
      funext x
      calc
        finCons x y i = finCons x y ((i.pred hi).succ) :=
          congrArg (finCons x y) (Fin.succ_pred i hi).symm
        _ = y (i.pred hi) := by
          simpa [finCons] using
            (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) x y (i.pred hi))
    rw [hfun]
    exact contDiff_const

lemma contDiff_fin_cons_rest {n : ℕ} (x : ℝ) :
    ContDiff ℝ 1 (fun y : Fin n → ℝ => finCons x y) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [finCons] using (contDiff_const : ContDiff ℝ 1 (fun _ : Fin n → ℝ => x))
  · have hfun : (fun y : Fin n → ℝ => finCons x y i) =
        fun y => y (i.pred hi) := by
      funext y
      calc
        finCons x y i = finCons x y ((i.pred hi).succ) :=
          congrArg (finCons x y) (Fin.succ_pred i hi).symm
        _ = y (i.pred hi) := by
          simpa [finCons] using
            (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) x y (i.pred hi))
    rw [hfun]
    exact contDiff_apply ℝ ℝ (i.pred hi)

lemma hasFDerivAt_fin_cons_rest {n : ℕ} (x : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => finCons x z)
      (finConsRestLinearMap n) y := by
  have hpi : HasFDerivAt (fun z : Fin n → ℝ => fun i => finCons x z i)
      (ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
        if hi : i = 0 then 0 else
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (i.pred hi)))) y := by
    rw [hasFDerivAt_pi]
    intro i
    by_cases hi : i = 0
    · subst i
      have hfun : (fun z : Fin n → ℝ => finCons x z 0) = fun _ => x := by
        funext z
        simp [finCons]
      rw [hfun]
      exact hasFDerivAt_const x y
    · have hfun : (fun z : Fin n → ℝ => finCons x z i) =
          fun z => z (i.pred hi) := by
        funext z
        calc
          finCons x z i = finCons x z ((i.pred hi).succ) := by
            exact congrArg (finCons x z) (Fin.succ_pred i hi).symm
          _ = z (i.pred hi) := by
            simpa [finCons] using
              (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) x z (i.pred hi))
      rw [hfun]
      rw [dite_eq_right hi]
      exact hasFDerivAt_apply (i.pred hi) y
  exact hpi

lemma finConsRestLinearMap_apply_single {n : ℕ} (j : Fin n) :
    finConsRestLinearMap n (Pi.single j 1) = Pi.single j.succ 1 := by
  apply funext
  intro i
  by_cases hi : i = 0
  · subst i
    simp [finConsRestLinearMap]
  · rw [finConsRestLinearMap, ContinuousLinearMap.pi_apply, dite_eq_right hi]
    simp only [ContinuousLinearMap.proj_apply]
    by_cases hji : i.pred hi = j
    · have hieq : i = j.succ := by
        calc
          i = (i.pred hi).succ := (Fin.succ_pred i hi).symm
          _ = j.succ := congrArg Fin.succ hji
      simp [hieq]
    · have hineq : i ≠ j.succ := by
        intro h
        apply hji
        have hj0 : j.succ ≠ (0 : Fin (n + 1)) := by simp
        simp [h]
      simp [hji, hineq]

lemma finConsRestLinearMap_norm_le (n : ℕ) :
    ‖finConsRestLinearMap n‖ ≤ 1 := by
  apply (finConsRestLinearMap n).opNorm_le_bound zero_le_one
  intro y
  have happly : finConsRestLinearMap n y = finCons 0 y := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [finConsRestLinearMap, finCons]
    · rw [finConsRestLinearMap, ContinuousLinearMap.pi_apply, dite_eq_right hi]
      simp only [ContinuousLinearMap.proj_apply]
      symm
      calc
        finCons 0 y i = finCons 0 y ((i.pred hi).succ) :=
          congrArg (finCons 0 y) (Fin.succ_pred i hi).symm
        _ = y (i.pred hi) := by
          simpa [finCons] using
            (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) 0 y (i.pred hi))
  rw [happly]
  simpa using (norm_fin_cons_le 0 y)

lemma fderiv_fin_cons_rest_norm_le {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (x : ℝ) (y : Fin n → ℝ) :
    ‖fderiv ℝ (fun z : Fin n → ℝ => f (finCons x z)) y‖ ≤
      ‖fderiv ℝ f (finCons x y)‖ := by
  have h := (hcont.differentiable one_ne_zero (finCons x y)).hasFDerivAt.comp
    y (hasFDerivAt_fin_cons_rest x y)
  have h' := h.fderiv
  have hfd : fderiv ℝ (fun z : Fin n → ℝ => f (finCons x z)) y =
      fderiv ℝ f (finCons x y) ∘SL finConsRestLinearMap n := by
    simpa [Function.comp_def] using h'
  rw [hfd]
  apply (fderiv ℝ f (finCons x y) ∘SL finConsRestLinearMap n).opNorm_le_bound
    (norm_nonneg _)
  intro z
  calc
    ‖(fderiv ℝ f (finCons x y) ∘SL finConsRestLinearMap n) z‖ =
        ‖fderiv ℝ f (finCons x y) (finConsRestLinearMap n z)‖ := by
      rw [ContinuousLinearMap.comp_apply]
    _ ≤ ‖fderiv ℝ f (finCons x y)‖ * ‖finConsRestLinearMap n z‖ :=
      ContinuousLinearMap.le_opNorm (fderiv ℝ f (finCons x y)) _
    _ ≤ ‖fderiv ℝ f (finCons x y)‖ *
        (‖finConsRestLinearMap n‖ * ‖z‖) := by
      exact mul_le_mul_of_nonneg_left
        ((finConsRestLinearMap n).le_opNorm z) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ f (finCons x y)‖ * ‖z‖ := by
      have hmul : ‖finConsRestLinearMap n‖ * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (finConsRestLinearMap_norm_le n) (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_left hmul (norm_nonneg _)).trans_eq (by ring)

lemma coordinateDerivative_fin_cons_rest {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (x : ℝ) (j : Fin n) (y : Fin n → ℝ) :
    coordinateDerivative (fun z : Fin n → ℝ => f (finCons x z)) j y =
      coordinateDerivative f j.succ (finCons x y) := by
  have h := (hcont.differentiable one_ne_zero (finCons x y)).hasFDerivAt.comp
    y (hasFDerivAt_fin_cons_rest x y)
  have h' := h.fderiv
  have hfd : fderiv ℝ (fun z : Fin n → ℝ => f (finCons x z)) y =
      fderiv ℝ f (finCons x y) ∘SL finConsRestLinearMap n := by
    simpa [Function.comp_def] using h'
  unfold coordinateDerivative
  rw [hfd, ContinuousLinearMap.comp_apply, finConsRestLinearMap_apply_single]

end RegularityStructures

end
