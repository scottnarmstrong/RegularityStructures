/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureRepresentation

/-!
# Concatenating two cylindrical coordinate lists

Two cylindrical representations are lifted to one finite vector by concatenating their test
functions.  The left and right projection maps are continuous linear maps, and their coordinate
derivatives are computed explicitly.  This is the finite-index transport needed to pass from the
fixed-coordinate uniqueness theorem to arbitrary representations in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

def malliavinConcatLeftCLM (n m : ℕ) :
    (Fin (n + m) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + m) => ℝ) (Fin.castAdd m i))

def malliavinConcatRightCLM (n m : ℕ) :
    (Fin (n + m) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + m) => ℝ) (Fin.natAdd n j))

def malliavinConcatTest {n m : ℕ} (h : Fin n → SpaceTime → ℝ)
    (k : Fin m → SpaceTime → ℝ) : Fin (n + m) → SpaceTime → ℝ :=
  Fin.addCases h k

theorem malliavinConcatLeftCLM_apply {n m : ℕ}
    (x : Fin (n + m) → ℝ) (i : Fin n) :
    malliavinConcatLeftCLM n m x i = x (Fin.castAdd m i) := rfl

theorem malliavinConcatRightCLM_apply {n m : ℕ}
    (x : Fin (n + m) → ℝ) (j : Fin m) :
    malliavinConcatRightCLM n m x j = x (Fin.natAdd n j) := rfl

private theorem malliavinConcatLeftCLM_single_left {n m : ℕ} (i : Fin n) :
    malliavinConcatLeftCLM n m (Pi.single (Fin.castAdd m i) (1 : ℝ)) = Pi.single i 1 := by
  classical
  funext j
  by_cases hij : i = j
  · subst j
    simp [malliavinConcatLeftCLM]
  · simp [malliavinConcatLeftCLM, hij]

private theorem malliavinConcatLeftCLM_single_right {n m : ℕ} (j : Fin m) :
    malliavinConcatLeftCLM n m (Pi.single (Fin.natAdd n j) (1 : ℝ)) = 0 := by
  funext i
  have hne : Fin.natAdd n j ≠ Fin.castAdd m i := by
    intro hij
    have hv := congrArg Fin.val hij
    simp at hv
    omega
  simp [malliavinConcatLeftCLM, hne]

private theorem malliavinConcatRightCLM_single_left {n m : ℕ} (i : Fin n) :
    malliavinConcatRightCLM n m (Pi.single (Fin.castAdd m i) (1 : ℝ)) = 0 := by
  funext j
  have hne : Fin.castAdd m i ≠ Fin.natAdd n j := by
    intro hij
    have hv := congrArg Fin.val hij
    simp at hv
    omega
  simp [malliavinConcatRightCLM, hne]

private theorem malliavinConcatRightCLM_single_right {n m : ℕ} (j : Fin m) :
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

private theorem coordinateDerivative_sub_concat_left {n m : ℕ}
    {f : (Fin n → ℝ) → ℝ} {g : (Fin m → ℝ) → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (i : Fin n) (x : Fin (n + m) → ℝ) :
    coordinateDerivative
        (fun y => f (malliavinConcatLeftCLM n m y) -
          g (malliavinConcatRightCLM n m y)) (Fin.castAdd m i) x =
      coordinateDerivative f i (malliavinConcatLeftCLM n m x) := by
  have hsub := ((hcont_f.comp (malliavinConcatLeftCLM n m).contDiff).differentiable
      one_ne_zero x).hasFDerivAt.sub
    ((hcont_g.comp (malliavinConcatRightCLM n m).contDiff).differentiable
      one_ne_zero x).hasFDerivAt
  have hsub' : HasFDerivAt
      (fun y => f (malliavinConcatLeftCLM n m y) -
        g (malliavinConcatRightCLM n m y))
      (fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x -
        fderiv ℝ (fun y => g (malliavinConcatRightCLM n m y)) x) x := by
    exact hsub
  have hfcomp : fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x =
      (fderiv ℝ f (malliavinConcatLeftCLM n m x)).comp
        (malliavinConcatLeftCLM n m) := by
    simpa [Function.comp_def] using
      fderiv_comp x hcont_f.contDiffAt.differentiableAt_one
        (malliavinConcatLeftCLM n m).hasFDerivAt.differentiableAt
  have hgcomp : fderiv ℝ (fun y => g (malliavinConcatRightCLM n m y)) x =
      (fderiv ℝ g (malliavinConcatRightCLM n m x)).comp
        (malliavinConcatRightCLM n m) := by
    simpa [Function.comp_def] using
      fderiv_comp x hcont_g.contDiffAt.differentiableAt_one
        (malliavinConcatRightCLM n m).hasFDerivAt.differentiableAt
  unfold coordinateDerivative
  rw [hsub'.fderiv, hfcomp, hgcomp, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, malliavinConcatLeftCLM_single_left,
    malliavinConcatRightCLM_single_left]
  simp

private theorem coordinateDerivative_sub_concat_right {n m : ℕ}
    {f : (Fin n → ℝ) → ℝ} {g : (Fin m → ℝ) → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (j : Fin m) (x : Fin (n + m) → ℝ) :
    coordinateDerivative
        (fun y => f (malliavinConcatLeftCLM n m y) -
          g (malliavinConcatRightCLM n m y)) (Fin.natAdd n j) x =
      -coordinateDerivative g j (malliavinConcatRightCLM n m x) := by
  have hsub := ((hcont_f.comp (malliavinConcatLeftCLM n m).contDiff).differentiable
      one_ne_zero x).hasFDerivAt.sub
    ((hcont_g.comp (malliavinConcatRightCLM n m).contDiff).differentiable
      one_ne_zero x).hasFDerivAt
  have hsub' : HasFDerivAt
      (fun y => f (malliavinConcatLeftCLM n m y) -
        g (malliavinConcatRightCLM n m y))
      (fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x -
        fderiv ℝ (fun y => g (malliavinConcatRightCLM n m y)) x) x := by
    exact hsub
  have hfcomp : fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y)) x =
      (fderiv ℝ f (malliavinConcatLeftCLM n m x)).comp
        (malliavinConcatLeftCLM n m) := by
    simpa [Function.comp_def] using
      fderiv_comp x hcont_f.contDiffAt.differentiableAt_one
        (malliavinConcatLeftCLM n m).hasFDerivAt.differentiableAt
  have hgcomp : fderiv ℝ (fun y => g (malliavinConcatRightCLM n m y)) x =
      (fderiv ℝ g (malliavinConcatRightCLM n m x)).comp
        (malliavinConcatRightCLM n m) := by
    simpa [Function.comp_def] using
      fderiv_comp x hcont_g.contDiffAt.differentiableAt_one
        (malliavinConcatRightCLM n m).hasFDerivAt.differentiableAt
  unfold coordinateDerivative
  rw [hsub'.fderiv, hfcomp, hgcomp, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, malliavinConcatLeftCLM_single_right,
    malliavinConcatRightCLM_single_right]
  simp

theorem cylindricalDerivative_eq_of_ae_eq_concat_coordinates
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n m : ℕ} {h : Fin n → SpaceTime → ℝ} {k : Fin m → SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ} {g : (Fin m → ℝ) → ℝ}
    {Z : Ω → Fin (n + m) → ℝ} {A : Matrix (Fin (n + m)) (Fin (n + m)) ℝ}
    (hZ : IsCentredGaussianVector P Z
      (fun i j => ∫ z, malliavinConcatTest h k i z * malliavinConcatTest h k j z))
    (hAsymm : A.IsSymm)
    (hAsq : A * A = fun i j =>
      ∫ z, malliavinConcatTest h k i z * malliavinConcatTest h k j z)
    (hlaw : P.map Z = (standardGaussianMeasure (n + m)).map
      (Matrix.mulVecLin A))
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (hgrowth_sub : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + m) → ℝ,
        |f (malliavinConcatLeftCLM n m x) -
            g (malliavinConcatRightCLM n m x)| +
          ‖fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y) -
            g (malliavinConcatRightCLM n m y)) x‖ ≤
          K * (1 + ‖x‖) ^ M)
    (hfg : cylindricalFunctional W h f =ᵐ[P] cylindricalFunctional W k g)
    (hcoord : ∀ (ω : Ω),
      (∀ i, Z ω (Fin.castAdd m i) = W (h i) ω) ∧
      (∀ j, Z ω (Fin.natAdd n j) = W (k j) ω))
    (hmem_h : ∀ i, MemLp (h i) 2) (hmem_k : ∀ j, MemLp (k j) 2)
    (hDsub : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W (malliavinConcatTest h k)
        (fun y => f (malliavinConcatLeftCLM n m y) -
          g (malliavinConcatRightCLM n m y)) p.1 p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2) =ᵐ[
      whiteNoiseDerivativeMeasure P]
      (fun p : Ω × SpaceTime => cylindricalDerivative W k g p.1 p.2) := by
  let H : (Fin (n + m) → ℝ) → ℝ := fun y =>
    f (malliavinConcatLeftCLM n m y) - g (malliavinConcatRightCLM n m y)
  have hmem_concat : ∀ i, MemLp (malliavinConcatTest h k i) 2 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [malliavinConcatTest] using hmem_h j
    · intro j
      simpa [malliavinConcatTest] using hmem_k j
  have hzero : H ∘ Z =ᵐ[P] 0 := by
    filter_upwards [hfg] with ω hω
    change f (fun i => W (h i) ω) = g (fun j => W (k j) ω) at hω
    change H (Z ω) = 0
    dsimp [H]
    have hleft : malliavinConcatLeftCLM n m (Z ω) =
        (fun i => W (h i) ω) := by
      funext i
      rw [malliavinConcatLeftCLM_apply, hcoord ω |>.1 i]
    have hright : malliavinConcatRightCLM n m (Z ω) =
        (fun j => W (k j) ω) := by
      funext j
      rw [malliavinConcatRightCLM_apply, hcoord ω |>.2 j]
    rw [hleft, hright]
    exact sub_eq_zero.mpr hω
  have hzero' : H ∘ Z =ᵐ[P] 0 := by
    exact hzero
  have hcontH : ContDiff ℝ 1 H := by
    dsimp [H]
    exact (hcont_f.comp (malliavinConcatLeftCLM n m).contDiff).sub
      (hcont_g.comp (malliavinConcatRightCLM n m).contDiff)
  have hcoordH : ∀ (ω : Ω) (i : Fin (n + m)),
      Z ω i = W (malliavinConcatTest h k i) ω := by
    intro ω i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [malliavinConcatTest] using (hcoord ω).1 j
    · intro j
      simpa [malliavinConcatTest] using (hcoord ω).2 j
  have hz := cylindricalDerivative_eq_zero_of_ae_eq_zero hZ hAsymm hAsq hlaw
    hcontH hgrowth_sub hzero' hcoordH hmem_concat
    hDsub
  filter_upwards [hz] with p hp
  have hident : cylindricalDerivative W (malliavinConcatTest h k) H p.1 p.2 =
      cylindricalDerivative W h f p.1 p.2 - cylindricalDerivative W k g p.1 p.2 := by
    unfold cylindricalDerivative H
    rw [Fin.sum_univ_add]
    change
      (∑ i : Fin n, coordinateDerivative
          (fun y => f (malliavinConcatLeftCLM n m y) -
            g (malliavinConcatRightCLM n m y)) (Fin.castAdd m i)
          (fun j => W (malliavinConcatTest h k j) p.1) *
        malliavinConcatTest h k (Fin.castAdd m i) p.2) +
      (∑ j : Fin m, coordinateDerivative
          (fun y => f (malliavinConcatLeftCLM n m y) -
            g (malliavinConcatRightCLM n m y)) (Fin.natAdd n j)
          (fun i => W (malliavinConcatTest h k i) p.1) *
        malliavinConcatTest h k (Fin.natAdd n j) p.2) =
      cylindricalDerivative W h f p.1 p.2 -
        cylindricalDerivative W k g p.1 p.2
    have hleft :
        (∑ i : Fin n, coordinateDerivative
            (fun y => f (malliavinConcatLeftCLM n m y) -
              g (malliavinConcatRightCLM n m y)) (Fin.castAdd m i)
            (fun j => W (malliavinConcatTest h k j) p.1) *
          malliavinConcatTest h k (Fin.castAdd m i) p.2) =
          cylindricalDerivative W h f p.1 p.2 := by
      unfold cylindricalDerivative
      apply Finset.sum_congr rfl
      intro i hi
      rw [coordinateDerivative_sub_concat_left hcont_f hcont_g]
      have harg : malliavinConcatLeftCLM n m
          (fun j => W (malliavinConcatTest h k j) p.1) =
          (fun j => W (h j) p.1) := by
        funext j
        rw [malliavinConcatLeftCLM_apply]
        simp [malliavinConcatTest]
      have htest : malliavinConcatTest h k (Fin.castAdd m i) p.2 = h i p.2 := by
        simp [malliavinConcatTest]
      rw [harg, htest]
    have hright :
        (∑ j : Fin m, coordinateDerivative
            (fun y => f (malliavinConcatLeftCLM n m y) -
              g (malliavinConcatRightCLM n m y)) (Fin.natAdd n j)
            (fun i => W (malliavinConcatTest h k i) p.1) *
          malliavinConcatTest h k (Fin.natAdd n j) p.2) =
          -cylindricalDerivative W k g p.1 p.2 := by
      unfold cylindricalDerivative
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [coordinateDerivative_sub_concat_right hcont_f hcont_g]
      have harg : malliavinConcatRightCLM n m
          (fun i => W (malliavinConcatTest h k i) p.1) =
          (fun i => W (k i) p.1) := by
        funext i
        rw [malliavinConcatRightCLM_apply]
        simp [malliavinConcatTest]
      have htest : malliavinConcatTest h k (Fin.natAdd n j) p.2 = k j p.2 := by
        simp [malliavinConcatTest]
      rw [harg, htest]
      ring
    rw [hleft, hright]
    ring
  rw [hident] at hp
  exact sub_eq_zero.mp hp

end RegularityStructures

end
