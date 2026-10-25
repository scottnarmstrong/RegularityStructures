/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincareN
public import RegularityStructures.Probability.CovarianceEnergy
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Independence.Integration
public import RegularityStructures.Probability.CylindricalFunctional

set_option linter.style.haveILetI false

/-!
# The covariance-form Gaussian Poincare inequality

The finite-dimensional standard inequality is transported through the square root of the
covariance matrix.  The law comparison is proved from the Gaussian characteristic-function
uniqueness theorem, with the coordinate convention `Fin n → ℝ` throughout.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped MatrixOrder

namespace RegularityStructures

private lemma strongDual_fin_apply {n : ℕ} (L : StrongDual ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → ℝ) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply]
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp
  calc
    L x = L (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) := congrArg L hx
    _ = ∑ i, x i * L (Pi.single i 1) := by
      rw [map_sum]
      simp_rw [map_smul]
      simp [smul_eq_mul]
    _ = ∑ i, L (Pi.single i 1) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

private lemma standardGaussian_coordinate_mean {n : ℕ} (i : Fin n) :
    ∫ x : Fin n → ℝ, x i ∂standardGaussianMeasure n = 0 := by
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hmp := measurePreserving_eval μ i
  have h := integral_map hmp.measurable.aemeasurable (by
    rw [hmp.map_eq]
    exact measurable_id.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  simpa [standardGaussianMeasure, μ] using h.symm

private lemma standardGaussian_coordinate_covariance {n : ℕ} (i j : Fin n) :
    cov[fun x : Fin n → ℝ => x i, fun x => x j; standardGaussianMeasure n] =
      if i = j then 1 else 0 := by
  haveI : IsProbabilityMeasure (standardGaussianMeasure n) := by
    dsimp [standardGaussianMeasure]
    infer_instance
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hmean (k : Fin n) : ∫ x : Fin n → ℝ, x k ∂standardGaussianMeasure n = 0 :=
    standardGaussian_coordinate_mean k
  have hcoord (k : Fin n) : MemLp (fun x : Fin n → ℝ => x k) 2
      (standardGaussianMeasure n) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval μ k)
    simpa [standardGaussianMeasure, μ, Function.comp_def] using h
  by_cases hij : i = j
  · subst j
    rw [covariance_self (hcoord i).aemeasurable]
    have hvar := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simp only [variance_id_gaussianReal, id_eq] at hvar
    rw [integral_id_gaussianReal] at hvar
    have hsq : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      simpa [Pi.pow_apply] using hvar.symm
    have hsq_map := integral_map (measurePreserving_eval μ i).measurable.aemeasurable (by
      rw [(measurePreserving_eval μ i).map_eq]
      exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.aestronglyMeasurable)
    rw [(measurePreserving_eval μ i).map_eq] at hsq_map
    rw [variance_eq_sub (hcoord i), hmean i]
    simp only [Pi.pow_apply]
    simpa [standardGaussianMeasure, μ, Function.comp_def, Pi.pow_apply, hsq] using hsq_map.symm
  · have hindep : iIndepFun (fun k (x : Fin n → ℝ) => x k)
        (standardGaussianMeasure n) := by
      simpa [standardGaussianMeasure, μ] using
        (iIndepFun_pi (fun _ => (aemeasurable_id : AEMeasurable (id : ℝ → ℝ)
          (gaussianReal 0 1))))
    have hm := (hindep.indepFun hij).integral_mul_eq_mul_integral
      ((measurable_pi_apply i).aestronglyMeasurable)
      ((measurable_pi_apply j).aestronglyMeasurable)
    rw [covariance_eq_sub (hcoord i) (hcoord j), hmean i, hmean j]
    simpa [hij, hmean i, hmean j, Pi.mul_apply] using hm

private lemma standardGaussian_coordinate_memLp {n : ℕ} (i : Fin n) :
    MemLp (fun x : Fin n → ℝ => x i) 2 (standardGaussianMeasure n) := by
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval μ i)
  simpa [standardGaussianMeasure, μ, Function.comp_def] using h

private lemma standardGaussian_linear_coordinate_covariance {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    cov[fun z : Fin n → ℝ => Matrix.mulVec A z i,
      fun z : Fin n → ℝ => Matrix.mulVec A z j; standardGaussianMeasure n] =
      ∑ a, A i a * A j a := by
  haveI : IsProbabilityMeasure (standardGaussianMeasure n) := by
    dsimp [standardGaussianMeasure]
    infer_instance
  have hsum := covariance_fun_sum_fun_sum
    (X := fun a (z : Fin n → ℝ) => A i a * z a)
    (Y := fun b (z : Fin n → ℝ) => A j b * z b)
    (fun a => (standardGaussian_coordinate_memLp a).const_mul _)
    (fun b => (standardGaussian_coordinate_memLp b).const_mul _)
  have hrewrite (k : Fin n) :
      (fun z : Fin n → ℝ => Matrix.mulVec A z k) =
        (fun z : Fin n → ℝ => ∑ a, A k a * z a) := by
    funext z
    rfl
  rw [hrewrite i, hrewrite j, hsum]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    standardGaussian_coordinate_covariance]
  simp [mul_ite]

private lemma covarianceBilinDual_eq_of_coordinate_data
    {n : ℕ} {μ ν : Measure (Fin n → ℝ)} [IsGaussian μ] [IsGaussian ν]
    (hcov : ∀ i j, cov[fun x : Fin n → ℝ => x i, fun x => x j; μ] =
      cov[fun x : Fin n → ℝ => x i, fun x => x j; ν]) :
    covarianceBilinDual μ = covarianceBilinDual ν := by
  have hμid : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) 2 μ :=
    IsGaussian.memLp_id μ 2 (by norm_num)
  have hνid : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) 2 ν :=
    IsGaussian.memLp_id ν 2 (by norm_num)
  have hcoordμ (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 2 μ := by
    let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    simpa [L, Function.comp_def] using hμid.continuousLinearMap_comp L
  have hcoordν (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 2 ν := by
    let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    simpa [L, Function.comp_def] using hνid.continuousLinearMap_comp L
  apply ContinuousLinearMap.ext
  intro L₁
  apply ContinuousLinearMap.ext
  intro L₂
  have hL₁ : (fun x : Fin n → ℝ => L₁ x) =
      (fun x => ∑ i, L₁ (Pi.single i 1) * x i) := by
    funext x
    exact strongDual_fin_apply L₁ x
  have hL₂ : (fun x : Fin n → ℝ => L₂ x) =
      (fun x => ∑ i, L₂ (Pi.single i 1) * x i) := by
    funext x
    exact strongDual_fin_apply L₂ x
  calc
    covarianceBilinDual μ L₁ L₂ = cov[L₁, L₂; μ] :=
      covarianceBilinDual_eq_covariance hμid L₁ L₂
    _ = cov[(fun x : Fin n → ℝ => L₁ x), (fun x : Fin n → ℝ => L₂ x); μ] := rfl
    _ = cov[fun x : Fin n → ℝ => ∑ i, L₁ (Pi.single i 1) * x i,
        fun x : Fin n → ℝ => ∑ j, L₂ (Pi.single j 1) * x j; μ] := by rw [hL₁, hL₂]
    _ = ∑ i, ∑ j, cov[fun x : Fin n → ℝ => L₁ (Pi.single i 1) * x i,
        fun x : Fin n → ℝ => L₂ (Pi.single j 1) * x j; μ] := by
      exact covariance_fun_sum_fun_sum
        (X := fun (i : Fin n) (x : Fin n → ℝ) => L₁ (Pi.single i 1) * x i)
        (Y := fun (j : Fin n) (x : Fin n → ℝ) => L₂ (Pi.single j 1) * x j)
        (fun i => (hcoordμ i).const_mul _)
        (fun j => (hcoordμ j).const_mul _)
    _ = ∑ i, ∑ j, (L₁ (Pi.single i 1) * L₂ (Pi.single j 1)) *
        cov[fun x : Fin n → ℝ => x i, fun x : Fin n → ℝ => x j; μ] := by
      simp_rw [covariance_const_mul_left, covariance_const_mul_right]
      ring_nf
    _ = ∑ i, ∑ j, (L₁ (Pi.single i 1) * L₂ (Pi.single j 1)) *
        cov[fun x : Fin n → ℝ => x i, fun x : Fin n → ℝ => x j; ν] := by
      simp_rw [hcov]
    _ = cov[fun x : Fin n → ℝ => ∑ i, L₁ (Pi.single i 1) * x i,
        fun x : Fin n → ℝ => ∑ j, L₂ (Pi.single j 1) * x j; ν] := by
      rw [covariance_fun_sum_fun_sum
        (X := fun (i : Fin n) (x : Fin n → ℝ) => L₁ (Pi.single i 1) * x i)
        (Y := fun (j : Fin n) (x : Fin n → ℝ) => L₂ (Pi.single j 1) * x j)
        (fun i => (hcoordν i).const_mul _)
        (fun j => (hcoordν j).const_mul _)]
      simp_rw [covariance_const_mul_left, covariance_const_mul_right]
      ring_nf
    _ = cov[(fun x : Fin n → ℝ => L₁ x), (fun x : Fin n → ℝ => L₂ x); ν] := by rw [hL₁, hL₂]
    _ = cov[L₁, L₂; ν] := rfl
    _ = covarianceBilinDual ν L₁ L₂ :=
      (covarianceBilinDual_eq_covariance hνid L₁ L₂).symm

private lemma centredGaussian_coordinate_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (i : Fin n) :
    MemLp (fun ω => X ω i) 2 P := by
  haveI : IsGaussian (P.map X) := hX.2.1
  have hmap : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) 2 (P.map X) :=
    IsGaussian.memLp_id (P.map X) 2 (by norm_num)
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [L, Function.comp_def] using hmap.comp_of_map hX.1 |>.continuousLinearMap_comp L

private lemma centredGaussian_law_coordinate_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (i : Fin n) :
    ∫ x, x i ∂P.map X = 0 := by
  have h := integral_map hX.1 (measurable_pi_apply i).aestronglyMeasurable
  simpa [Function.comp_def] using h.trans (hX.2.2.1 i)

private lemma centredGaussian_law_coordinate_covariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (i j : Fin n) :
    cov[fun x : Fin n → ℝ => x i, fun x => x j; P.map X] = C i j := by
  haveI : IsGaussian (P.map X) := hX.2.1
  haveI : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    calc
      P Set.univ = (P.map X) Set.univ := by
        rw [Measure.map_apply_of_aemeasurable hX.1 MeasurableSet.univ]
        simp
      _ = 1 := measure_univ
  have hmap := covariance_map_fun (μ := P) (X := fun x : Fin n → ℝ => x i)
    (Y := fun x => x j) (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable hX.1
  rw [hmap]
  rw [covariance_eq_sub (centredGaussian_coordinate_memLp hX i)
    (centredGaussian_coordinate_memLp hX j)]
  simp only [Pi.mul_apply]
  rw [hX.2.2.2 i j, hX.2.2.1 i, hX.2.2.1 j]
  simp

private lemma centredGaussian_covariance_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) :
    Matrix.PosSemidef (C : Matrix (Fin n) (Fin n) ℝ) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hsym : C j i = C i j := by
      calc
        C j i = ∫ ω, X ω j * X ω i ∂P := (hX.2.2.2 j i).symm
        _ = ∫ ω, X ω i * X ω j ∂P := by
          congr 1
          funext ω
          ring
        _ = C i j := hX.2.2.2 i j
    rw [hsym]
    simp
  · intro v
    have hv := variance_nonneg (fun ω => ∑ i, v i * X ω i) P
    rw [centredGaussian_linear_variance_eq_covarianceEnergy hX v] at hv
    simpa [covarianceEnergy, dotProduct, Matrix.mulVec, starRingEnd_apply] using hv

private lemma integral_id_eq_zero_of_coordinate_mean {n : ℕ} {μ : Measure (Fin n → ℝ)}
    [IsGaussian μ] (hmean : ∀ i, ∫ x, x i ∂μ = 0) :
    ∫ x, x ∂μ = 0 := by
  have hId : Integrable (id : (Fin n → ℝ) → (Fin n → ℝ)) μ := IsGaussian.integrable_id
  ext i
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.integral_comp_comm hId
  simpa [Function.id_def, L] using (h.symm.trans (hmean i))

private lemma matrix_factor_energy {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hAsq : A * A = C)
    (hAsymm : A.IsSymm) (b : Fin n → ℝ) :
    ∑ i, (∑ k, b k * A k i) ^ 2 = covarianceEnergy C b := by
  classical
  unfold covarianceEnergy
  calc
    ∑ i, (∑ k, b k * A k i) ^ 2 =
        ∑ i, ∑ k, ∑ l, (b k * A k i) * (b l * A l i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ k, ∑ l, ∑ i, (b k * A k i) * (b l * A l i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, b k * (∑ i, A k i * A l i) * b l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      calc
        ∑ i, (b k * A k i) * (b l * A l i) =
            ∑ i, b k * (A k i * A l i) * b l := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = b k * (∑ i, A k i * A l i) * b l := by
          calc
            ∑ i, b k * (A k i * A l i) * b l =
                ∑ i, b k * ((A k i * A l i) * b l) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = b k * ∑ i, (A k i * A l i) * b l := by
              rw [Finset.mul_sum]
            _ = b k * (∑ i, A k i * A l i) * b l := by
              have hsum := Finset.sum_mul (Finset.univ : Finset (Fin n))
                (fun i => A k i * A l i) (b l)
              rw [← hsum]
              ring
    _ = ∑ k, ∑ l, b k * C k l * b l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      congr 2
      calc
        ∑ i, A k i * A l i = ∑ i, A k i * A i l := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hAsymm.apply l i]
        _ = (A * A) k l := by simp [Matrix.mul_apply]
        _ = C k l := by rw [hAsq]
    _ = ∑ k, b k * ∑ l, C k l * b l := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem gaussian_poincare_centredGaussianVector {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C)
    {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M) :
    Var[fun ω => f (X ω); P] ≤
      ∫ ω, covarianceEnergy C (fun i => coordinateDerivative f i (X ω)) ∂P := by
  have hCpos := centredGaussian_covariance_pos hX
  let Cmat : Matrix (Fin n) (Fin n) ℝ := C
  have hCmat : Matrix.PosSemidef Cmat := by
    simpa [Cmat] using hCpos
  let A : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt Cmat
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  have hAsqrt : A ^ 2 = Cmat := by
    dsimp [A]
    exact CFC.sq_sqrt Cmat hCmat.nonneg
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact CFC.sqrt_nonneg Cmat
  have hAsymm : A.IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact (Matrix.nonneg_iff_posSemidef.mp hAnonneg).1
  have hL_apply (z : Fin n → ℝ) : L z = Matrix.mulVec A z := by
    rfl
  haveI : IsGaussian (P.map X) := hX.2.1
  haveI : IsGaussian (standardGaussianMeasure n) := isGaussian_standardGaussianMeasure n
  haveI : IsGaussian ((standardGaussianMeasure n).map L) := inferInstance
  have hmeanμ : ∫ y, y ∂P.map X = 0 :=
    integral_id_eq_zero_of_coordinate_mean
      (fun i => centredGaussian_law_coordinate_mean hX i)
  have hmeanstd : ∫ y, y ∂standardGaussianMeasure n = 0 :=
    integral_id_eq_zero_of_coordinate_mean standardGaussian_coordinate_mean
  have hmeanmap : ∫ y, y ∂(standardGaussianMeasure n).map L = 0 := by
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id L]
    rw [hmeanstd, map_zero]
  have hAsq : A * A = Cmat := by
    simpa [pow_two] using hAsqrt
  have hmatrix_cov (i j : Fin n) : ∑ a, A i a * A j a = C i j := by
    calc
      ∑ a, A i a * A j a = ∑ a, A i a * A a j := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAsymm.apply j a]
      _ = (A * A) i j := by simp [Matrix.mul_apply]
      _ = Cmat i j := by rw [hAsq]
      _ = C i j := rfl
  have hcov_law (i j : Fin n) :
      cov[fun y : Fin n → ℝ => y i, fun y => y j; P.map X] =
        cov[fun y : Fin n → ℝ => y i, fun y => y j;
          (standardGaussianMeasure n).map L] := by
    have hmap := covariance_map_fun (μ := standardGaussianMeasure n)
      (X := fun y : Fin n → ℝ => y i) (Y := fun y => y j)
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
      L.continuous.measurable.aemeasurable
    calc
      cov[fun y : Fin n → ℝ => y i, fun y => y j; P.map X] = C i j :=
        centredGaussian_law_coordinate_covariance hX i j
      _ = ∑ a, A i a * A j a := (hmatrix_cov i j).symm
      _ = cov[fun y : Fin n → ℝ => y i, fun y => y j;
          (standardGaussianMeasure n).map L] := by
        rw [hmap]
        rw [show (fun z : Fin n → ℝ => (L z) i) =
            (fun z => Matrix.mulVec A z i) by
          funext z
          rw [hL_apply]]
        rw [show (fun z : Fin n → ℝ => (L z) j) =
            (fun z => Matrix.mulVec A z j) by
          funext z
          rw [hL_apply]]
        exact (standardGaussian_linear_coordinate_covariance A i j).symm
  have hcovdual : covarianceBilinDual (P.map X) =
      covarianceBilinDual ((standardGaussianMeasure n).map L) :=
    covarianceBilinDual_eq_of_coordinate_data hcov_law
  have hlaw : P.map X = (standardGaussianMeasure n).map L :=
    IsGaussian.ext_covarianceBilinDual (hmeanμ.trans hmeanmap.symm) hcovdual
  let g : (Fin n → ℝ) → ℝ := fun z => f (L z)
  have hgcont : ContDiff ℝ 1 g := by
    exact hcont.comp L.contDiff
  have hderiv_comp (z : Fin n → ℝ) :
      fderiv ℝ g z = (fderiv ℝ f (L z)).comp L := by
    simpa [g, Function.comp_def] using
      fderiv_comp z hcont.contDiffAt.differentiableAt_one
        L.hasFDerivAt.differentiableAt
  rcases hgrowth with ⟨K, M, hK, hgrowth⟩
  have hvalue (x : Fin n → ℝ) : |f x| ≤ K * (1 + ‖x‖) ^ M := by
    exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ f x))).trans (hgrowth x)
  have hderiv (x : Fin n → ℝ) : ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M := by
    exact (le_add_of_nonneg_left (abs_nonneg (f x))).trans (hgrowth x)
  have hbase (z : Fin n → ℝ) :
      1 + ‖L z‖ ≤ (1 + ‖L‖) * (1 + ‖z‖) := by
    have hz := L.le_opNorm z
    nlinarith [norm_nonneg (L z), norm_nonneg z, norm_nonneg L]
  have hpoly (z : Fin n → ℝ) :
      (1 + ‖L z‖) ^ M ≤
        (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M := by
    calc
      (1 + ‖L z‖) ^ M ≤ ((1 + ‖L‖) * (1 + ‖z‖)) ^ M :=
        pow_le_pow_left₀ (by positivity) (hbase z) M
      _ = (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M := by rw [mul_pow]
  have hderiv_g (z : Fin n → ℝ) :
      ‖fderiv ℝ g z‖ ≤ K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M * ‖L‖ := by
    rw [hderiv_comp]
    calc
      ‖(fderiv ℝ f (L z)).comp L‖ ≤ ‖fderiv ℝ f (L z)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * (1 + ‖L z‖) ^ M * ‖L‖ :=
        mul_le_mul_of_nonneg_right (hderiv (L z)) (norm_nonneg L)
      _ ≤ K * ((1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M) * ‖L‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpoly z) hK) (norm_nonneg L)
      _ = K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M * ‖L‖ := by ring
  have hgrowth_g : ∃ D : ℝ, ∃ N : ℕ, 0 ≤ D ∧
      ∀ z : Fin n → ℝ, |g z| + ‖fderiv ℝ g z‖ ≤ D * (1 + ‖z‖) ^ N := by
    refine ⟨K * (1 + ‖L‖) ^ M * (1 + ‖L‖), M, ?_, ?_⟩
    · positivity
    · intro z
      have hv : |g z| ≤ K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M := by
        dsimp [g]
        calc
          |f (L z)| ≤ K * (1 + ‖L z‖) ^ M := hvalue (L z)
          _ ≤ K * ((1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M) := by
            exact mul_le_mul_of_nonneg_left (hpoly z) hK
          _ = K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M := by ring
      have hd := hderiv_g z
      calc
        |g z| + ‖fderiv ℝ g z‖ ≤
            K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M +
              K * (1 + ‖L‖) ^ M * (1 + ‖z‖) ^ M * ‖L‖ :=
          add_le_add hv hd
        _ = K * (1 + ‖L‖) ^ M * (1 + ‖L‖) * (1 + ‖z‖) ^ M := by ring
  have hstd := gaussian_poincare_standard hgcont hgrowth_g
  have hL_single (i : Fin n) :
      L (Pi.single i 1) = fun k => A k i := by
    rw [hL_apply]
    funext k
    simp [Matrix.col_apply]
  have hcoord_g (i : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative g i z =
        ∑ k, coordinateDerivative f k (L z) * A k i := by
    rw [coordinateDerivative, hderiv_comp]
    rw [ContinuousLinearMap.comp_apply, hL_single]
    rw [strongDual_fin_apply]
    simp [coordinateDerivative]
  have henergy (z : Fin n → ℝ) :
      ∑ i, coordinateDerivative g i z ^ 2 =
        covarianceEnergy C (fun k => coordinateDerivative f k (L z)) := by
    calc
      ∑ i, coordinateDerivative g i z ^ 2 =
          ∑ i, (∑ k, coordinateDerivative f k (L z) * A k i) ^ 2 := by
        simp_rw [hcoord_g]
      _ = covarianceEnergy C (fun k => coordinateDerivative f k (L z)) := by
        simpa [Cmat] using
          (matrix_factor_energy hAsq hAsymm
            (fun k => coordinateDerivative f k (L z)))
  have hvar : Var[fun ω => f (X ω); P] = Var[g; standardGaussianMeasure n] := by
    calc
      Var[fun ω => f (X ω); P] = Var[f; P.map X] := by
        simpa [Function.comp_def] using
          (variance_map hcont.continuous.measurable.aemeasurable hX.1).symm
      _ = Var[f; (standardGaussianMeasure n).map L] := by rw [hlaw]
      _ = Var[f ∘ L; standardGaussianMeasure n] := by
        rw [variance_map hcont.continuous.measurable.aemeasurable
          L.continuous.measurable.aemeasurable]
      _ = Var[g; standardGaussianMeasure n] := by rfl
  have hcoordcont (i : Fin n) :
      Continuous (fun y : Fin n → ℝ => coordinateDerivative f i y) := by
    have h := hcont.continuous_fderiv_apply one_ne_zero
    simpa [coordinateDerivative, Function.comp_def] using h.comp
      (by fun_prop : Continuous (fun y : Fin n → ℝ => (y, Pi.single i 1)))
  let q : (Fin n → ℝ) → ℝ := fun y =>
    covarianceEnergy C (fun i => coordinateDerivative f i y)
  have hqcont : Continuous q := by
    unfold q covarianceEnergy
    apply continuous_finsetSum _
    intro i hi
    apply (hcoordcont i).mul
    apply continuous_finsetSum _
    intro j hj
    exact continuous_const.mul (hcoordcont j)
  have hqmeas : Measurable q := hqcont.measurable
  have hqmapL :
      ∫ y, q y ∂(standardGaussianMeasure n).map L =
        ∫ z, q (L z) ∂standardGaussianMeasure n := by
    exact integral_map L.continuous.measurable.aemeasurable
      hqmeas.aestronglyMeasurable
  have hqmapX :
      ∫ y, q y ∂P.map X = ∫ ω, q (X ω) ∂P := by
    exact integral_map hX.1 hqmeas.aestronglyMeasurable
  have hstdq :
      ∫ z, coordinateEnergy g z ∂standardGaussianMeasure n =
        ∫ z, q (L z) ∂standardGaussianMeasure n := by
    apply integral_congr_ae
    filter_upwards [] with z
    simpa [coordinateEnergy, q] using henergy z
  calc
    Var[fun ω => f (X ω); P] = Var[g; standardGaussianMeasure n] := hvar
    _ ≤ ∫ z, coordinateEnergy g z ∂standardGaussianMeasure n := hstd
    _ = ∫ z, q (L z) ∂standardGaussianMeasure n := hstdq
    _ = ∫ y, q y ∂(standardGaussianMeasure n).map L := hqmapL.symm
    _ = ∫ y, q y ∂P.map X := by rw [hlaw]
    _ = ∫ ω, q (X ω) ∂P := hqmapX
    _ = ∫ ω, covarianceEnergy C
        (fun i => coordinateDerivative f i (X ω)) ∂P := by rfl

end RegularityStructures

end
