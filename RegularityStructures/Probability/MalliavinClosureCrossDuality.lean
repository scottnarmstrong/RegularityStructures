/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureGaussianAuto
public import RegularityStructures.Probability.MalliavinClosureRandomTest
public import RegularityStructures.Probability.MalliavinClosureConcatenation

/-!
# Cross-coordinate Gaussian duality

This file transports the random-test identity to two independent cylindrical coordinate lists.
The graph functional may depend on `h`, while the smooth random coefficient may depend on `k`.
Their coordinate lists are concatenated, and the finite-dimensional Gaussian IBP identity is
left as an explicit hypothesis in the algebraic theorem below.  The growth-based Gaussian
instance is supplied in the next theorem.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

private theorem malliavin_cross_left_single {n m : ℕ} (i : Fin n) :
    malliavinConcatLeftCLM n m (Pi.single (Fin.castAdd m i) (1 : ℝ)) = Pi.single i 1 := by
  classical
  funext j
  by_cases hij : i = j
  · subst j
    simp [malliavinConcatLeftCLM]
  · simp [malliavinConcatLeftCLM, hij]

private theorem malliavin_cross_left_right_single {n m : ℕ} (j : Fin m) :
    malliavinConcatLeftCLM n m (Pi.single (Fin.natAdd n j) (1 : ℝ)) = 0 := by
  funext i
  have hne : Fin.natAdd n j ≠ Fin.castAdd m i := by
    intro hij
    have hv := congrArg Fin.val hij
    simp at hv
    omega
  simp [malliavinConcatLeftCLM, hne]

private theorem malliavin_cross_right_left_single {n m : ℕ} (i : Fin n) :
    malliavinConcatRightCLM n m (Pi.single (Fin.castAdd m i) (1 : ℝ)) = 0 := by
  funext j
  have hne : Fin.castAdd m i ≠ Fin.natAdd n j := by
    intro hij
    have hv := congrArg Fin.val hij
    simp at hv
    omega
  simp [malliavinConcatRightCLM, hne]

private theorem malliavin_cross_right_single {n m : ℕ} (j : Fin m) :
    malliavinConcatRightCLM n m (Pi.single (Fin.natAdd n j) (1 : ℝ)) = Pi.single j 1 := by
  classical
  funext l
  by_cases hjl : j = l
  · subst l
    simp [malliavinConcatRightCLM]
  · have hjl' : Fin.natAdd n j ≠ Fin.natAdd n l := by
      intro h
      have hv := congrArg Fin.val h
      apply hjl
      exact Fin.ext (by simpa using hv)
    simp [malliavinConcatRightCLM, hjl, hjl']

private theorem malliavin_cross_left_concat_test
    {Ω : Type*} {n m : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (h : Fin n → SpaceTime → ℝ) (k : Fin m → SpaceTime → ℝ) (ω : Ω) :
    malliavinConcatLeftCLM n m
        (fun i => W (malliavinConcatTest h k i) ω) =
      (fun i => W (h i) ω) := by
  funext i
  rw [malliavinConcatLeftCLM_apply]
  simp [malliavinConcatTest]

private theorem malliavin_cross_right_concat_test
    {Ω : Type*} {n m : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (h : Fin n → SpaceTime → ℝ) (k : Fin m → SpaceTime → ℝ) (ω : Ω) :
    malliavinConcatRightCLM n m
        (fun i => W (malliavinConcatTest h k i) ω) =
      (fun j => W (k j) ω) := by
  funext j
  rw [malliavinConcatRightCLM_apply]
  simp [malliavinConcatTest]

private theorem malliavin_cross_deriv_left
    {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (i : Fin n) (x : Fin (n + m) → ℝ) :
    coordinateDerivative (fun y => f (malliavinConcatLeftCLM n m y))
        (Fin.castAdd m i) x =
      coordinateDerivative f i (malliavinConcatLeftCLM n m x) := by
  have hcomp := fderiv_comp x hcont.contDiffAt.differentiableAt_one
    (malliavinConcatLeftCLM n m).hasFDerivAt.differentiableAt
  have hcomp' : fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x =
      (fderiv ℝ f (malliavinConcatLeftCLM n m x)).comp
        (malliavinConcatLeftCLM n m) := by
    simpa [Function.comp_def] using hcomp
  unfold coordinateDerivative
  rw [hcomp',
    ContinuousLinearMap.comp_apply, malliavin_cross_left_single]

private theorem malliavin_cross_deriv_right_zero
    {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (j : Fin m) (x : Fin (n + m) → ℝ) :
    coordinateDerivative (fun y => f (malliavinConcatLeftCLM n m y))
        (Fin.natAdd n j) x = 0 := by
  have hcomp := fderiv_comp x hcont.contDiffAt.differentiableAt_one
    (malliavinConcatLeftCLM n m).hasFDerivAt.differentiableAt
  have hcomp' : fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x =
      (fderiv ℝ f (malliavinConcatLeftCLM n m x)).comp
        (malliavinConcatLeftCLM n m) := by
    simpa [Function.comp_def] using hcomp
  unfold coordinateDerivative
  rw [hcomp',
    ContinuousLinearMap.comp_apply, malliavin_cross_left_right_single]
  simp

private theorem malliavin_cross_deriv_left_zero
    {n m : ℕ} {u : (Fin m → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 u) (i : Fin n) (x : Fin (n + m) → ℝ) :
    coordinateDerivative (fun y => u (malliavinConcatRightCLM n m y))
        (Fin.castAdd m i) x = 0 := by
  have hcomp := fderiv_comp x hcont.contDiffAt.differentiableAt_one
    (malliavinConcatRightCLM n m).hasFDerivAt.differentiableAt
  have hcomp' : fderiv ℝ (fun y => u (malliavinConcatRightCLM n m y)) x =
      (fderiv ℝ u (malliavinConcatRightCLM n m x)).comp
        (malliavinConcatRightCLM n m) := by
    simpa [Function.comp_def] using hcomp
  unfold coordinateDerivative
  rw [hcomp',
    ContinuousLinearMap.comp_apply, malliavin_cross_right_left_single]
  simp

private theorem malliavin_cross_deriv_right
    {n m : ℕ} {u : (Fin m → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 u) (j : Fin m) (x : Fin (n + m) → ℝ) :
    coordinateDerivative (fun y => u (malliavinConcatRightCLM n m y))
        (Fin.natAdd n j) x =
      coordinateDerivative u j (malliavinConcatRightCLM n m x) := by
  have hcomp := fderiv_comp x hcont.contDiffAt.differentiableAt_one
    (malliavinConcatRightCLM n m).hasFDerivAt.differentiableAt
  have hcomp' : fderiv ℝ (fun y => u (malliavinConcatRightCLM n m y)) x =
      (fderiv ℝ u (malliavinConcatRightCLM n m x)).comp
        (malliavinConcatRightCLM n m) := by
    simpa [Function.comp_def] using hcomp
  unfold coordinateDerivative
  rw [hcomp',
    ContinuousLinearMap.comp_apply, malliavin_cross_right_single]

theorem malliavin_cross_random_test_duality_of_ibp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} {n m : ℕ}
    {h : Fin n → SpaceTime → ℝ} {k : Fin m → SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ} {u : (Fin m → ℝ) → ℝ}
    {r : SpaceTime → ℝ}
    (hmem_h : ∀ i, MemLp (h i) 2) (hmem_k : ∀ j, MemLp (k j) 2)
    (hmem_r : MemLp r 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_u : ContDiff ℝ 1 u)
    (hgrad : ∀ i, Integrable
      (fun ω => coordinateDerivative f i (fun j => W (h j) ω) *
        u (fun j => W (k j) ω)) P)
    (hfdu : ∀ j, Integrable
      (fun ω => f (fun i => W (h i) ω) *
        coordinateDerivative u j (fun i => W (k i) ω)) P)
    (hfuW : Integrable
      (fun ω => (f (fun i => W (h i) ω) * u (fun j => W (k j) ω)) * W r ω) P)
    (hIBP : ∫ ω,
        (fun x => f (malliavinConcatLeftCLM n m x) *
          u (malliavinConcatRightCLM n m x))
          (fun i => W (malliavinConcatTest h k i) ω) * W r ω ∂P =
      ∑ i, (∫ ω, coordinateDerivative
          (fun x => f (malliavinConcatLeftCLM n m x) *
            u (malliavinConcatRightCLM n m x)) i
            (fun j => W (malliavinConcatTest h k j) ω) ∂P) *
        ∫ z, malliavinConcatTest h k i z * r z) :
    ∫ p, cylindricalDerivative W h f p.1 p.2 *
        (u (fun i => W (k i) p.1) * r p.2) ∂(whiteNoiseDerivativeMeasure P) =
      ∫ ω, f (fun i => W (h i) ω) *
        (u (fun j => W (k j) ω) * W r ω -
          ∑ j, (∫ z, k j z * r z) *
            coordinateDerivative u j (fun i => W (k i) ω)) ∂P := by
  let H : Fin (n + m) → SpaceTime → ℝ := malliavinConcatTest h k
  let F : (Fin (n + m) → ℝ) → ℝ := fun x =>
    f (malliavinConcatLeftCLM n m x)
  let U : (Fin (n + m) → ℝ) → ℝ := fun x =>
    u (malliavinConcatRightCLM n m x)
  have hmem_H : ∀ i, MemLp (H i) 2 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [H, malliavinConcatTest] using hmem_h j
    · intro j
      simpa [H, malliavinConcatTest] using hmem_k j
  have hcont_F : ContDiff ℝ 1 F := by
    exact hcont_f.comp (malliavinConcatLeftCLM n m).contDiff
  have hcont_U : ContDiff ℝ 1 U := by
    exact hcont_u.comp (malliavinConcatRightCLM n m).contDiff
  have hgrad' : ∀ i, Integrable
      (fun ω => coordinateDerivative F i (fun j => W (H j) ω) *
        U (fun j => W (H j) ω)) P := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have heq : (fun ω => coordinateDerivative F (Fin.castAdd m j)
          (fun i => W (H i) ω) * U (fun i => W (H i) ω)) =
          (fun ω => coordinateDerivative f j (fun i => W (h i) ω) *
            u (fun i => W (k i) ω)) := by
        funext ω
        dsimp [F, U, H]
        rw [malliavin_cross_deriv_left hcont_f j]
        rw [malliavin_cross_left_concat_test h k ω,
          malliavin_cross_right_concat_test h k ω]
      rw [heq]
      exact hgrad j
    · intro j
      simp [F, U, H, malliavinConcatTest,
        malliavin_cross_deriv_right_zero hcont_f j]
  have hfdu' : ∀ i, Integrable
      (fun ω => F (fun j => W (H j) ω) *
        coordinateDerivative U i (fun j => W (H j) ω)) P := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [F, U, H, malliavinConcatTest,
        malliavin_cross_deriv_left_zero hcont_u j]
    · intro j
      have heq : (fun ω => F (fun i => W (H i) ω) *
          coordinateDerivative U (Fin.natAdd n j) (fun i => W (H i) ω)) =
          (fun ω => f (fun i => W (h i) ω) *
            coordinateDerivative u j (fun i => W (k i) ω)) := by
        funext ω
        dsimp [F, U, H]
        rw [malliavin_cross_deriv_right hcont_u j]
        rw [malliavin_cross_left_concat_test h k ω,
          malliavin_cross_right_concat_test h k ω]
      rw [heq]
      exact hfdu j
  have hfuW' : Integrable
      (fun ω => (F (fun j => W (H j) ω) * U (fun j => W (H j) ω)) * W r ω) P := by
    have heq : (fun ω => (F (fun j => W (H j) ω) * U (fun j => W (H j) ω)) * W r ω) =
        (fun ω => (f (fun i => W (h i) ω) * u (fun j => W (k j) ω)) * W r ω) := by
      funext ω
      dsimp [F, U, H]
      rw [malliavin_cross_left_concat_test h k ω,
        malliavin_cross_right_concat_test h k ω]
    rw [heq]
    exact hfuW
  have hpair := malliavin_random_test_duality_of_ibp
    (W := W) (h := H) (f := F) (u := U) (k := r)
    hmem_H hmem_r hcont_F hcont_U hgrad' hfdu' hfuW'
    (by simpa [F, U, H] using hIBP)
  have hleft : (fun p : Ω × SpaceTime =>
      cylindricalDerivative W H F p.1 p.2 *
        (U (fun i => W (H i) p.1) * r p.2)) =
      (fun p : Ω × SpaceTime =>
        cylindricalDerivative W h f p.1 p.2 *
          (u (fun i => W (k i) p.1) * r p.2)) := by
    funext p
    unfold cylindricalDerivative F U H
    rw [Fin.sum_univ_add]
    rw [malliavin_cross_right_concat_test h k p.1]
    change
      ((∑ i : Fin n, coordinateDerivative
          (fun y => f (malliavinConcatLeftCLM n m y)) (Fin.castAdd m i)
          (fun j => W (malliavinConcatTest h k j) p.1) *
        malliavinConcatTest h k (Fin.castAdd m i) p.2) +
        (∑ j : Fin m, coordinateDerivative
          (fun y => f (malliavinConcatLeftCLM n m y)) (Fin.natAdd n j)
          (fun i => W (malliavinConcatTest h k i) p.1) *
        malliavinConcatTest h k (Fin.natAdd n j) p.2)) *
        (u (fun i => W (k i) p.1) * r p.2) =
      (∑ i : Fin n, coordinateDerivative f i (fun j => W (h j) p.1) *
        h i p.2) * (u (fun i => W (k i) p.1) * r p.2)
    have hleft_sum :
        (∑ i : Fin n, coordinateDerivative
            (fun y => f (malliavinConcatLeftCLM n m y)) (Fin.castAdd m i)
            (fun j => W (malliavinConcatTest h k j) p.1) *
          malliavinConcatTest h k (Fin.castAdd m i) p.2) =
          ∑ i : Fin n, coordinateDerivative f i (fun j => W (h j) p.1) *
            h i p.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [malliavin_cross_deriv_left hcont_f]
      rw [malliavin_cross_left_concat_test h k p.1]
      simp [malliavinConcatTest]
    have hright_sum :
        (∑ j : Fin m, coordinateDerivative
            (fun y => f (malliavinConcatLeftCLM n m y)) (Fin.natAdd n j)
            (fun i => W (malliavinConcatTest h k i) p.1) *
          malliavinConcatTest h k (Fin.natAdd n j) p.2) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [malliavin_cross_deriv_right_zero hcont_f]
      simp
    rw [hleft_sum, hright_sum]
    simp
  rw [hleft] at hpair
  have hsumU (ω : Ω) :
      ∑ i, (∫ z, H i z * r z) * coordinateDerivative U i
          (fun j => W (H j) ω) =
        ∑ j, (∫ z, k j z * r z) *
          coordinateDerivative u j (fun i => W (k i) ω) := by
    rw [Fin.sum_univ_add]
    change
      (∑ i : Fin n, (∫ z, H (Fin.castAdd m i) z * r z) *
          coordinateDerivative U (Fin.castAdd m i)
            (fun j => W (H j) ω)) +
        ∑ j : Fin m, (∫ z, H (Fin.natAdd n j) z * r z) *
          coordinateDerivative U (Fin.natAdd n j)
            (fun i => W (H i) ω) =
      ∑ j, (∫ z, k j z * r z) *
        coordinateDerivative u j (fun i => W (k i) ω)
    have hleft_zero : ∑ i : Fin n,
        (∫ z, H (Fin.castAdd m i) z * r z) * coordinateDerivative U
          (Fin.castAdd m i) (fun j => W (H j) ω) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      dsimp [U]
      rw [malliavin_cross_deriv_left_zero hcont_u]
      simp
    have hright : ∑ j : Fin m,
        (∫ z, H (Fin.natAdd n j) z * r z) * coordinateDerivative U
          (Fin.natAdd n j) (fun i => W (H i) ω) =
        ∑ j, (∫ z, k j z * r z) *
          coordinateDerivative u j (fun i => W (k i) ω) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [U]
      rw [malliavin_cross_deriv_right hcont_u]
      rw [malliavin_cross_right_concat_test h k ω]
      simp [H, malliavinConcatTest]
    rw [hleft_zero, zero_add]
    exact hright
  have hright : (fun ω => F (fun j => W (H j) ω) *
      (U (fun j => W (H j) ω) * W r ω -
        ∑ i, (∫ z, H i z * r z) *
          coordinateDerivative U i (fun j => W (H j) ω))) =
      (fun ω => f (fun i => W (h i) ω) *
        (u (fun j => W (k j) ω) * W r ω -
          ∑ j, (∫ z, k j z * r z) *
            coordinateDerivative u j (fun i => W (k i) ω))) := by
    funext ω
    rw [hsumU]
    dsimp [F, U, H]
    rw [malliavin_cross_left_concat_test h k ω,
      malliavin_cross_right_concat_test h k ω]
  rw [hright] at hpair
  exact hpair

end RegularityStructures

end
