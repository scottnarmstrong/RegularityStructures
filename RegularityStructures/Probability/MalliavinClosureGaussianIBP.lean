/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincareCovariance
public import RegularityStructures.Probability.GaussianVector
public import RegularityStructures.Probability.MalliavinClosureCore
import Mathlib.Analysis.Matrix.PosDef

/-!
# Gaussian integration by parts for a linearly represented vector

The cylindrical derivative is identified through the Gaussian integration-by-parts identity.  This
file isolates the finite-dimensional calculation.  A centred Gaussian vector represented as
`A Z`, where `Z` has the product standard Gaussian law, satisfies

`E[Xⱼ f(X)] = ∑ᵢ Cⱼᵢ E[∂ᵢ f(X)]`.

The polynomial-growth and all integrability hypotheses are explicit.  The standard Gaussian
integration-by-parts theorem used here is the finite-dimensional theorem proved in
`standardGaussianIntegrationByParts`, corresponding to [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

private lemma matrix_mulVecLin_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (i : Fin n) :
    Matrix.mulVecLin A z i = ∑ k, A i k * z k := by
  rfl

private lemma continuousLinearMap_fin_apply {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
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

private lemma coordinateDerivative_continuous_local {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hcont : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x => coordinateDerivative f i x) := by
  have h := hcont.continuous_fderiv_apply one_ne_zero
  simpa [coordinateDerivative, Function.comp_def] using h.comp
    (by fun_prop : Continuous (fun x : Fin n → ℝ => (x, Pi.single i 1)))

private lemma coordinateDerivative_comp_matrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (z : Fin n → ℝ) (j : Fin n) :
    coordinateDerivative (fun y => f (Matrix.mulVec A y)) j z =
      ∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i j := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  have hL (y : Fin n → ℝ) : L y = Matrix.mulVec A y := by rfl
  have hcomp := fderiv_comp z hcont.contDiffAt.differentiableAt_one
    L.hasFDerivAt.differentiableAt
  rw [show (fun y => f (Matrix.mulVec A y)) = f ∘ L by
    funext y
    rfl]
  rw [coordinateDerivative, hcomp]
  rw [L.hasFDerivAt.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  have hsingle (j : Fin n) : L (Pi.single j 1) = fun i => A i j := by
    rw [hL]
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp
  rw [hsingle]
  rw [continuousLinearMap_fin_apply]
  simp only [coordinateDerivative]
  rw [hL z]

private lemma gaussian_ibp_matrix_energy {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hAsq : A * A = C)
    (hAsymm : A.IsSymm) (b : Fin n → ℝ) (j : Fin n) :
    ∑ k, A k j * ∑ i, b i * A i k =
      ∑ i, C j i * b i := by
  classical
  calc
    ∑ k, A k j * ∑ i, b i * A i k =
        ∑ i, ∑ k, A k j * (b i * A i k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i, (∑ k, A k j * A i k) * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ k, A k j * (b i * A i k) =
            ∑ k, (A k j * A i k) * b i := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k, A k j * A i k) * b i := by
          rw [Finset.sum_mul]
    _ = ∑ i, (∑ k, A j k * A k i) * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun x => x * b i)
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hAsymm.apply j k, ← hAsymm.apply i k]
    _ = ∑ i, C j i * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Matrix.mul_apply, hAsq]

theorem gaussian_vector_integration_by_parts_of_standard_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Ω → Fin n → ℝ} {C A : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsCentredGaussianVector P X C)
    (hAsymm : A.IsSymm) (hAsq : A * A = C)
    (hlaw : P.map X = (standardGaussianMeasure n).map
      (Matrix.mulVecLin A))
    {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (_hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_g : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin n → ℝ, |f (Matrix.mulVec A z)| +
        ‖fderiv ℝ (fun y => f (Matrix.mulVec A y)) z‖ ≤ K * (1 + ‖z‖) ^ M)
    (hint_f : Integrable (fun ω => f (X ω)) P)
    (hint_deriv : ∀ i, Integrable
      (fun ω => coordinateDerivative f i (X ω)) P)
    (_hint_x : ∀ i, Integrable
      (fun ω => X ω i * f (X ω)) P)
    (_hint_f_std : Integrable
      (fun z : Fin n → ℝ => f (Matrix.mulVec A z))
        (standardGaussianMeasure n))
    (_hint_deriv_std : ∀ i, Integrable
      (fun z : Fin n → ℝ => coordinateDerivative f i (Matrix.mulVec A z))
        (standardGaussianMeasure n))
    (hint_x_std : ∀ i, Integrable
      (fun z : Fin n → ℝ =>
        z i * f (Matrix.mulVec A z))
        (standardGaussianMeasure n))
    (hint_f_density : Integrable
      (fun z : Fin n → ℝ =>
        f (Matrix.mulVec A z) * standardGaussianDensityReal z) volume)
    (hint_deriv_density : ∀ i, Integrable
      (fun z : Fin n → ℝ =>
        coordinateDerivative f i (Matrix.mulVec A z) *
          standardGaussianDensityReal z) volume)
    (hint_x_density : ∀ i, Integrable
      (fun z : Fin n → ℝ =>
        z i * f (Matrix.mulVec A z) * standardGaussianDensityReal z) volume) :
    ∀ j, ∫ ω, X ω j * f (X ω) ∂P =
      ∑ i, C j i * ∫ ω, coordinateDerivative f i (X ω) ∂P := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  let g : (Fin n → ℝ) → ℝ := fun z => f (Matrix.mulVec A z)
  have hL_meas : AEMeasurable (Matrix.mulVecLin A)
      (standardGaussianMeasure n) := by
    exact L.continuous.measurable.aemeasurable
  have hcontg : ContDiff ℝ 1 g := by
    dsimp [g]
    exact hcont.comp L.contDiff
  have hderivg (j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative g j z =
        ∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i j := by
    exact coordinateDerivative_comp_matrix hcont z j
  have hstd_ibp : ∀ j, ∫ z, z j * g z ∂standardGaussianMeasure n =
      ∫ z, coordinateDerivative g j z ∂standardGaussianMeasure n := by
    intro j
    apply standardGaussianIntegrationByParts hcontg
    · exact hgrowth_g
    · simpa [g] using hint_f_density
    · intro i
      rw [show (fun z => coordinateDerivative g i z * standardGaussianDensityReal z) =
        (fun z => (∑ k, coordinateDerivative f k (Matrix.mulVec A z) * A k i) *
          standardGaussianDensityReal z) by
          funext z; rw [hderivg]]
      simp_rw [Finset.sum_mul]
      apply integrable_finsetSum
      intro k hk
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hint_deriv_density k).const_mul (A k i)
    · simpa [g] using hint_x_density
  have hderiv_map (i : Fin n) :
      Integrable (fun y : Fin n → ℝ => coordinateDerivative f i y)
        (P.map X) := by
    apply (integrable_map_measure
      (coordinateDerivative_continuous_local hcont i).measurable.aestronglyMeasurable hX.1).2
    simpa [Function.comp_def] using hint_deriv i
  have hderiv_std_map (i : Fin n) :
      Integrable (fun y : Fin n → ℝ => coordinateDerivative f i y)
        ((standardGaussianMeasure n).map (Matrix.mulVecLin A)) := by
    rw [← hlaw]
    exact hderiv_map i
  have hderiv_comp (i : Fin n) :
      Integrable (fun z : Fin n → ℝ => coordinateDerivative f i (Matrix.mulVec A z))
        (standardGaussianMeasure n) := by
    have hmap : Integrable (fun y : Fin n → ℝ => coordinateDerivative f i y)
        (Measure.map (⇑L) (standardGaussianMeasure n)) := by
      simpa [L] using hderiv_std_map i
    have h := (integrable_map_measure
      (coordinateDerivative_continuous_local hcont i).measurable.aestronglyMeasurable
        L.continuous.measurable.aemeasurable).1
      hmap
    simpa [Function.comp_def, L] using h
  have hF_map : Integrable (fun y : Fin n → ℝ => f y) (P.map X) := by
    exact (integrable_map_measure hcont.continuous.measurable.aestronglyMeasurable hX.1).2
      (by simpa [Function.comp_def] using hint_f)
  have hF_std_map : Integrable (fun y : Fin n → ℝ => f y)
      ((standardGaussianMeasure n).map (Matrix.mulVecLin A)) := by
    rw [← hlaw]
    exact hF_map
  have hleft_map (j : Fin n) :
      ∫ z, (Matrix.mulVec A z) j * g z ∂standardGaussianMeasure n =
        ∫ ω, X ω j * f (X ω) ∂P := by
    have hfun : (fun y : Fin n → ℝ => y j * f y) =
        fun y => (fun y : Fin n → ℝ => y j) y * f y := rfl
    calc
      ∫ z, (Matrix.mulVec A z) j * g z ∂standardGaussianMeasure n =
          ∫ y, y j * f y ∂((standardGaussianMeasure n).map (Matrix.mulVecLin A)) := by
        simpa [g, L, Function.comp_def] using
          (integral_map hL_meas
            ((measurable_pi_apply j).mul hcont.continuous.measurable).aestronglyMeasurable).symm
      _ = ∫ y, y j * f y ∂(P.map X) := by rw [hlaw]
      _ = ∫ ω, X ω j * f (X ω) ∂P := by
        simpa [Function.comp_def] using
          (integral_map hX.1
            ((measurable_pi_apply j).mul hcont.continuous.measurable).aestronglyMeasurable)
  have hderiv_integral (i : Fin n) :
      ∫ z, coordinateDerivative f i (Matrix.mulVec A z) ∂standardGaussianMeasure n =
        ∫ ω, coordinateDerivative f i (X ω) ∂P := by
    calc
      ∫ z, coordinateDerivative f i (Matrix.mulVec A z) ∂standardGaussianMeasure n =
          ∫ y, coordinateDerivative f i y ∂
            ((standardGaussianMeasure n).map (Matrix.mulVecLin A)) := by
        simpa [L, Function.comp_def] using
          (integral_map hL_meas
            (coordinateDerivative_continuous_local hcont i).measurable.aestronglyMeasurable).symm
      _ = ∫ y, coordinateDerivative f i y ∂(P.map X) := by rw [hlaw]
      _ = ∫ ω, coordinateDerivative f i (X ω) ∂P := by
        simpa [Function.comp_def] using
          (integral_map hX.1
            (coordinateDerivative_continuous_local hcont i).measurable.aestronglyMeasurable)
  have hderivg_integral (k : Fin n) :
      ∫ z, coordinateDerivative g k z ∂standardGaussianMeasure n =
        ∑ i, (∫ ω, coordinateDerivative f i (X ω) ∂P) * A i k := by
    rw [show (fun z => coordinateDerivative g k z) =
      fun z => ∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i k by
        funext z; rw [hderivg]]
    rw [integral_finsetSum]
    · simp_rw [integral_mul_const, hderiv_integral]
    · intro i hi
      simpa [mul_comm] using (hderiv_comp i).const_mul _
  intro j
  calc
    ∫ ω, X ω j * f (X ω) ∂P =
        ∫ z, (Matrix.mulVec A z) j * g z ∂standardGaussianMeasure n :=
      (hleft_map j).symm
    _ = ∑ k, A j k * ∫ z, z k * g z ∂standardGaussianMeasure n := by
      rw [show (fun z => (Matrix.mulVec A z) j * g z) =
        fun z => ∑ k, A j k * (z k * g z) by
          funext z
          simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]]
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro k hk
        simpa [mul_assoc, mul_comm] using (hint_x_std k).const_mul (A j k)
    _ = ∑ k, A j k * ∫ z, coordinateDerivative g k z
        ∂standardGaussianMeasure n := by
      simp_rw [hstd_ibp]
    _ = ∑ i, C j i * ∫ ω, coordinateDerivative f i (X ω) ∂P := by
      simp_rw [hderivg_integral]
      calc
        ∑ k, A j k * ∑ i, (∫ ω, coordinateDerivative f i (X ω) ∂P) * A i k =
            ∑ k, A k j * ∑ i, (∫ ω, coordinateDerivative f i (X ω) ∂P) * A i k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hAsymm.apply j k]
        _ = ∑ i, C j i * ∫ ω, coordinateDerivative f i (X ω) ∂P :=
          gaussian_ibp_matrix_energy hAsq hAsymm
            (fun i => ∫ ω, coordinateDerivative f i (X ω) ∂P) j

end RegularityStructures

end
