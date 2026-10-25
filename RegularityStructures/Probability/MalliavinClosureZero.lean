/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureSupport
public import RegularityStructures.Probability.MalliavinClosureGaussianIBP

/-!
# Vanishing of a cylindrical derivative

This module proves the finite-dimensional support step needed for representation independence.  If
a smooth cylindrical function vanishes almost surely, its derivative vanishes in the white-noise
`L²` space.  The proof transports the null set to a standard Gaussian representation, uses full
support and the chain rule, and then converts the covariance energy back to the spatial square
integral.  All `MemLp` and Gaussian-law hypotheses are explicit.  The argument is the finite
Gaussian core of [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma ae_eq_zero_of_integral_sq_zero_local {P : Measure Ω} {u : Ω → ℝ}
    (hu : Integrable (fun ω => u ω ^ 2) P)
    (hzero : ∫ ω, u ω ^ 2 ∂P = 0) : u =ᵐ[P] 0 := by
  have hnonneg : 0 ≤ᵐ[P] (fun ω => u ω ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hsq : (fun ω => u ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hu).mp hzero
  filter_upwards [hsq] with ω hω
  exact sq_eq_zero_iff.mp hω

private lemma continuousLinearMap_fin_apply_local {n : ℕ}
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

private lemma matrix_factor_energy_zero {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hAsq : A * A = C)
    (hAsymm : A.IsSymm) (b : Fin n → ℝ)
    (hzero : ∀ j, (∑ k, b k * A k j) ^ 2 = 0) :
    covarianceEnergy C b = 0 := by
  have hfactor : ∑ j, (∑ k, b k * A k j) ^ 2 = covarianceEnergy C b := by
    unfold covarianceEnergy
    calc
      ∑ j, (∑ k, b k * A k j) ^ 2 =
          ∑ j, ∑ k, ∑ l, (b k * A k j) * (b l * A l j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_two, Finset.sum_mul_sum]
      _ = ∑ k, ∑ l, ∑ j, (b k * A k j) * (b l * A l j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ l, b k * (∑ j, A k j * A l j) * b l := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        calc
          ∑ j, (b k * A k j) * (b l * A l j) =
              ∑ j, b k * (A k j * A l j) * b l := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = b k * (∑ j, A k j * A l j) * b l := by
            calc
              ∑ j, b k * (A k j * A l j) * b l =
                  ∑ j, b k * ((A k j * A l j) * b l) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
              _ = b k * ∑ j, (A k j * A l j) * b l := by
                rw [Finset.mul_sum]
              _ = b k * (∑ j, A k j * A l j) * b l := by
                have hsum := Finset.sum_mul (Finset.univ : Finset (Fin n))
                  (fun j => A k j * A l j) (b l)
                rw [← hsum]
                ring
      _ = ∑ k, ∑ l, b k * C k l * b l := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        congr 2
        calc
          ∑ j, A k j * A l j = ∑ j, A k j * A j l := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hAsymm.apply l j]
          _ = (A * A) k l := by simp [Matrix.mul_apply]
          _ = C k l := by rw [hAsq]
      _ = ∑ k, b k * ∑ l, C k l * b l := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
  calc
    covarianceEnergy C b = ∑ j, (∑ k, b k * A k j) ^ 2 := hfactor.symm
    _ = 0 := Finset.sum_eq_zero (fun j hj => hzero j)

private lemma coordinateDerivative_comp_matrix_local {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (z : Fin n → ℝ) (j : Fin n) :
    coordinateDerivative (fun y => f (Matrix.mulVec A y)) j z =
      ∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i j := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  have hcomp := fderiv_comp z hcont.contDiffAt.differentiableAt_one
    L.hasFDerivAt.differentiableAt
  rw [show (fun y => f (Matrix.mulVec A y)) = f ∘ L by
    funext y
    rfl]
  rw [coordinateDerivative, hcomp, L.hasFDerivAt.fderiv,
    ContinuousLinearMap.comp_apply]
  have hsingle (j : Fin n) :
      L (Pi.single j (1 : ℝ) : Fin n → ℝ) = fun i : Fin n => A i j := by
    funext i
    change ∑ x : Fin n, A i x *
      ((Pi.single j (1 : ℝ) : Fin n → ℝ) x) = A i j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp
  rw [hsingle]
  rw [continuousLinearMap_fin_apply_local]
  simp only [coordinateDerivative]
  rw [show L z = Matrix.mulVec A z by rfl]

theorem cylindricalDerivative_eq_zero_of_ae_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    {X : Ω → Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsCentredGaussianVector P X
      (fun i j => ∫ z, h i z * h j z))
    (hAsymm : A.IsSymm)
    (hAsq : A * A = fun i j => ∫ z, h i z * h j z)
    (hlaw : P.map X = (standardGaussianMeasure n).map
      (Matrix.mulVecLin A))
    (hcont : ContDiff ℝ 1 f)
    (_hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hzero : f ∘ X =ᵐ[P] 0)
    (hcoord : ∀ (ω : Ω) (i : Fin n), X ω i = W (h i) ω)
    (hmem : ∀ i, MemLp (h i) 2)
    (hD : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P)) :
    (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2) =ᵐ[
      whiteNoiseDerivativeMeasure P] 0 := by
  let g : (Fin n → ℝ) → ℝ := fun z => f (Matrix.mulVec A z)
  have hzero_raw : ∀ᵐ ω ∂P, f (X ω) = 0 := by
    filter_upwards [hzero] with ω hω
    change f (X ω) = 0 at hω
    exact hω
  have hzero_map : ∀ᵐ x ∂P.map X, f x = 0 := by
    apply (ae_map_iff hX.1 (measurableSet_preimage hcont.continuous.measurable
      (measurableSet_singleton 0))).2
    exact hzero_raw
  have hzero_std_map : ∀ᵐ x ∂(standardGaussianMeasure n).map
      (Matrix.mulVecLin A), f x = 0 := by
    rw [← hlaw]
    exact hzero_map
  have hzero_std : g =ᵐ[standardGaussianMeasure n] 0 := by
    have h := ae_of_ae_map
      (Matrix.mulVecLin A).toContinuousLinearMap.continuous.aemeasurable hzero_std_map
    filter_upwards [h] with z hz
    simpa [g] using hz
  have hzero_g : g = 0 := standardGaussian_continuous_ae_eq_zero
    (hcont.comp (Matrix.mulVecLin A).toContinuousLinearMap.contDiff).continuous hzero_std
  have hgrad_zero (j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative g j z = 0 := by
    rw [hzero_g]
    simp [coordinateDerivative]
  have hcoordg (j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative g j z =
        ∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i j := by
    exact coordinateDerivative_comp_matrix_local hcont z j
  have hfactor_zero (j : Fin n) (z : Fin n → ℝ) :
      (∑ i, coordinateDerivative f i (Matrix.mulVec A z) * A i j) ^ 2 = 0 := by
    rw [← hcoordg j z, hgrad_zero]
    simp
  have hq_std_zero (z : Fin n → ℝ) :
      covarianceEnergy (fun i j => ∫ y, h i y * h j y)
        (fun i => coordinateDerivative f i (Matrix.mulVec A z)) = 0 := by
    exact matrix_factor_energy_zero hAsq hAsymm _ (fun j => hfactor_zero j z)
  let q : (Fin n → ℝ) → ℝ := fun x => covarianceEnergy
    (fun i j => ∫ y, h i y * h j y) (fun i => coordinateDerivative f i x)
  have hqcont : Continuous q := by
    have hcoordcont (i : Fin n) :
        Continuous (fun x : Fin n → ℝ => coordinateDerivative f i x) := by
      have h := hcont.continuous_fderiv_apply one_ne_zero
      simpa [coordinateDerivative, Function.comp_def] using h.comp
        (by fun_prop : Continuous (fun x : Fin n → ℝ => (x, Pi.single i 1)))
    unfold q covarianceEnergy
    apply continuous_finsetSum
    intro i hi
    apply (hcoordcont i).mul
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (hcoordcont j)
  have hq_std_map : ∀ᵐ x ∂(standardGaussianMeasure n).map
      (Matrix.mulVecLin A), q x = 0 := by
    have hz : ∀ᵐ z ∂standardGaussianMeasure n, q (Matrix.mulVec A z) = 0 := by
      filter_upwards [] with z
      exact hq_std_zero z
    apply (ae_map_iff (Matrix.mulVecLin A).toContinuousLinearMap.continuous.aemeasurable
      (measurableSet_preimage hqcont.measurable (measurableSet_singleton 0))).2
    simpa [Function.comp_def] using hz
  have hq_map : ∀ᵐ x ∂P.map X, q x = 0 := by
    rw [hlaw]
    exact hq_std_map
  have hq_zero : ∀ᵐ ω ∂P, q (X ω) = 0 :=
    ae_of_ae_map hX.1 hq_map
  have hinner (ω : Ω) :
      ∫ z, (cylindricalDerivative W h f ω z) ^ 2 = q (X ω) := by
    have hgrad : (fun i => coordinateDerivative f i
        (fun j => W (h j) ω)) = (fun i => coordinateDerivative f i (X ω)) := by
      funext i
      congr 2
      funext j
      rw [← hcoord ω j]
    change ∫ z, (∑ i, coordinateDerivative f i
      (fun j => W (h j) ω) * h i z) ^ 2 = q (X ω)
    rw [cylindrical_energy_eq_integral_sq (a := fun i =>
      coordinateDerivative f i (fun j => W (h j) ω)) hmem]
    rw [hgrad]
  have htotal :
      ∫ p, (cylindricalDerivative W h f p.1 p.2) ^ 2 ∂
        (whiteNoiseDerivativeMeasure P) = 0 := by
    change ∫ p, (cylindricalDerivative W h f p.1 p.2) ^ 2 ∂
      (P.prod (volume : Measure SpaceTime)) = 0
    rw [integral_prod _ hD.integrable_sq]
    apply integral_eq_zero_of_ae
    filter_upwards [hq_zero] with ω hω
    change (∫ z, (cylindricalDerivative W h f ω z) ^ 2) = 0
    rw [hinner ω, hω]
  exact ae_eq_zero_of_integral_sq_zero_local hD.integrable_sq htotal

end RegularityStructures

end
