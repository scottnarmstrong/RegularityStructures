/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Probability.Independence.Integration
public import RegularityStructures.Probability.CovarianceEnergy
public import RegularityStructures.Probability.GaussianLaw

set_option linter.style.haveILetI false

/-!
# Standard representation of a centred finite Gaussian vector

This module supplies the finite-dimensional law comparison needed by the cylindrical Malliavin
calculus. A centred Gaussian vector with covariance `C` is represented in law as `A Z`, where `Z`
has the product standard Gaussian law and `A` is the symmetric positive square root of `C`. The
proof uses only the strengthened `IsCentredGaussianVector` from
`RegularityStructures.Probability.WhiteNoise`, and is the finite-dimensional Gaussian representation
behind [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace RegularityStructures

private lemma centredGaussian_covariance_pos_local
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
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

private lemma standardGaussian_coordinate_mean_local {n : ℕ} (i : Fin n) :
    ∫ x : Fin n → ℝ, x i ∂standardGaussianMeasure n = 0 := by
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hmp := measurePreserving_eval μ i
  have h := integral_map hmp.measurable.aemeasurable (by
    rw [hmp.map_eq]
    exact measurable_id.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  simpa [standardGaussianMeasure, μ] using h.symm

private lemma standardGaussian_coordinate_covariance_local {n : ℕ} (i j : Fin n) :
    cov[fun x : Fin n → ℝ => x i, fun x => x j; standardGaussianMeasure n] =
      if i = j then 1 else 0 := by
  haveI : IsProbabilityMeasure (standardGaussianMeasure n) := by
    dsimp [standardGaussianMeasure]
    infer_instance
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hmean (k : Fin n) : ∫ x : Fin n → ℝ, x k ∂standardGaussianMeasure n = 0 :=
    standardGaussian_coordinate_mean_local k
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

private lemma standardGaussian_linear_coordinate_covariance_local {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    cov[fun z : Fin n → ℝ => Matrix.mulVec A z i,
      fun z : Fin n → ℝ => Matrix.mulVec A z j; standardGaussianMeasure n] =
      ∑ a, A i a * A j a := by
  haveI : IsProbabilityMeasure (standardGaussianMeasure n) := by
    dsimp [standardGaussianMeasure]
    infer_instance
  have hcoord (k : Fin n) : MemLp (fun z : Fin n → ℝ => z k) 2
      (standardGaussianMeasure n) := by
    let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval μ k)
    simpa [standardGaussianMeasure, μ, Function.comp_def] using h
  have hsum := covariance_fun_sum_fun_sum
    (X := fun a (z : Fin n → ℝ) => A i a * z a)
    (Y := fun b (z : Fin n → ℝ) => A j b * z b)
    (fun a => (hcoord a).const_mul _)
    (fun b => (hcoord b).const_mul _)
  have hrewrite (k : Fin n) :
      (fun z : Fin n → ℝ => Matrix.mulVec A z k) =
        (fun z : Fin n → ℝ => ∑ a, A k a * z a) := by
    funext z
    rfl
  rw [hrewrite i, hrewrite j, hsum]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    standardGaussian_coordinate_covariance_local]
  simp [mul_ite]

private lemma strongDual_fin_apply_local {n : ℕ} (L : StrongDual ℝ (Fin n → ℝ))
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

private lemma covarianceBilinDual_eq_of_coordinate_data_local
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
    exact strongDual_fin_apply_local L₁ x
  have hL₂ : (fun x : Fin n → ℝ => L₂ x) =
      (fun x => ∑ i, L₂ (Pi.single i 1) * x i) := by
    funext x
    exact strongDual_fin_apply_local L₂ x
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

private lemma centredGaussian_law_coordinate_covariance_local
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
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
  have hXlp : MemLp X 2 P := by
    have hmap : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) 2 (P.map X) :=
      IsGaussian.memLp_id (P.map X) 2 (by norm_num)
    simpa only [Function.id_comp] using hmap.comp_of_map hX.1
  have hcoord (k : Fin n) : MemLp (fun ω => X ω k) 2 P := by
    let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
    simpa [L, Function.comp_def] using hXlp.continuousLinearMap_comp L
  rw [covariance_eq_sub (hcoord i) (hcoord j)]
  simp only [Pi.mul_apply]
  rw [hX.2.2.2 i j, hX.2.2.1 i, hX.2.2.1 j]
  simp

private lemma centredGaussian_law_coordinate_mean_local
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (i : Fin n) :
    ∫ x, x i ∂P.map X = 0 := by
  have h := integral_map hX.1 (measurable_pi_apply i).aestronglyMeasurable
  simpa [Function.comp_def] using h.trans (hX.2.2.1 i)

private lemma integral_id_eq_zero_of_coordinate_mean_local {n : ℕ}
    {μ : Measure (Fin n → ℝ)} [IsGaussian μ]
    (hmean : ∀ i, ∫ x, x i ∂μ = 0) :
    ∫ x, x ∂μ = 0 := by
  have hId : Integrable (id : (Fin n → ℝ) → (Fin n → ℝ)) μ := IsGaussian.integrable_id
  ext i
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.integral_comp_comm hId
  simpa [Function.id_def, L] using (h.symm.trans (hmean i))

theorem centredGaussianVector_standard_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsSymm ∧ A * A = C ∧
        P.map X = (standardGaussianMeasure n).map (Matrix.mulVecLin A) := by
  let Cmat : Matrix (Fin n) (Fin n) ℝ := C
  have hCmat : Matrix.PosSemidef Cmat := by
    simpa [Cmat] using centredGaussian_covariance_pos_local hX
  let A : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt Cmat
  have hAsqrt : A ^ 2 = Cmat := by
    dsimp [A]
    exact CFC.sq_sqrt Cmat hCmat.nonneg
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact CFC.sqrt_nonneg Cmat
  have hAsymm : A.IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact (Matrix.nonneg_iff_posSemidef.mp hAnonneg).1
  have hAsq : A * A = Cmat := by
    simpa [pow_two] using hAsqrt
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  have hL_apply (z : Fin n → ℝ) : L z = Matrix.mulVec A z := by
    rfl
  letI : IsGaussian (P.map X) := hX.2.1
  letI : IsGaussian (standardGaussianMeasure n) := isGaussian_standardGaussianMeasure n
  letI : IsGaussian ((standardGaussianMeasure n).map L) := inferInstance
  have hmeanμ : ∫ y, y ∂P.map X = 0 :=
    integral_id_eq_zero_of_coordinate_mean_local
      (fun i => centredGaussian_law_coordinate_mean_local hX i)
  have hmeanstd : ∫ y, y ∂standardGaussianMeasure n = 0 :=
    integral_id_eq_zero_of_coordinate_mean_local standardGaussian_coordinate_mean_local
  have hmeanmap : ∫ y, y ∂(standardGaussianMeasure n).map L = 0 := by
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id L]
    rw [hmeanstd, map_zero]
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
        centredGaussian_law_coordinate_covariance_local hX i j
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
        exact (standardGaussian_linear_coordinate_covariance_local A i j).symm
  have hcovdual : covarianceBilinDual (P.map X) =
      covarianceBilinDual ((standardGaussianMeasure n).map L) :=
    covarianceBilinDual_eq_of_coordinate_data_local hcov_law
  have hlaw : P.map X = (standardGaussianMeasure n).map L :=
    IsGaussian.ext_covarianceBilinDual (hmeanμ.trans hmeanmap.symm) hcovdual
  refine ⟨A, hAsymm, ?_, ?_⟩
  · simpa [Cmat] using hAsq
  · simpa [L, hL_apply]

end RegularityStructures

end
