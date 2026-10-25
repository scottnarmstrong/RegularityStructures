/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureGaussianIBP
public import RegularityStructures.Probability.SpectralGap
public import RegularityStructures.Probability.CylindricalFunctional

/-!
# Gaussian IBP duality for a cylindrical derivative

The finite-dimensional Gaussian integration-by-parts theorem is transported to an augmented
vector whose zeroth coordinate is `W k` and whose remaining coordinates are `W (h i)`.  The
result is the duality identity behind the cylindrical Malliavin derivative.  The standard
representation and all integrability data are parameters: these are the exact analytic
hypotheses used by the finite-dimensional IBP theorem, rather than an implicit admissibility
predicate.  See [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous linear map which forgets the zeroth coordinate. -/
def malliavinTailCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ)

theorem malliavinTailCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    malliavinTailCLM n x i = x i.succ := rfl

/-- Lift a function of the tail coordinates to a function of a vector with one extra coordinate. -/
def malliavinTailLift {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    (Fin (n + 1) → ℝ) → ℝ :=
  fun x => f (malliavinTailCLM n x)

theorem malliavinTailLift_apply {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (x : Fin (n + 1) → ℝ) :
    malliavinTailLift f x = f (fun i => x i.succ) := by
  rfl

private theorem malliavinTailCLM_single_zero {n : ℕ} :
    malliavinTailCLM n (Pi.single (0 : Fin (n + 1)) 1) = 0 := by
  funext i
  simp [malliavinTailCLM]

private theorem malliavinTailCLM_single_succ {n : ℕ} (i : Fin n) :
    malliavinTailCLM n (Pi.single i.succ 1) = Pi.single i 1 := by
  classical
  funext j
  by_cases hij : i = j
  · subst j
    simp [malliavinTailCLM]
  · have hij' : i.succ ≠ j.succ := by
      intro h
      exact hij (Fin.succ_injective n h)
    simp [malliavinTailCLM, hij, hij']

theorem coordinateDerivative_malliavinTailLift_zero {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hcont : ContDiff ℝ 1 f)
    (x : Fin (n + 1) → ℝ) :
    coordinateDerivative (malliavinTailLift f) 0 x = 0 := by
  have hfd := (hcont.differentiable one_ne_zero (malliavinTailCLM n x)).hasFDerivAt.comp
    x (malliavinTailCLM n).hasFDerivAt
  have hfd' : fderiv ℝ (malliavinTailLift f) x =
      (fderiv ℝ f (malliavinTailCLM n x)).comp (malliavinTailCLM n) := by
    change fderiv ℝ (fun y => f (malliavinTailCLM n y)) x = _
    exact hfd.fderiv
  unfold coordinateDerivative
  rw [hfd', ContinuousLinearMap.comp_apply, malliavinTailCLM_single_zero]
  simp

theorem coordinateDerivative_malliavinTailLift_succ {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hcont : ContDiff ℝ 1 f)
    (i : Fin n) (x : Fin (n + 1) → ℝ) :
    coordinateDerivative (malliavinTailLift f) i.succ x =
      coordinateDerivative f i (malliavinTailCLM n x) := by
  have hfd := (hcont.differentiable one_ne_zero (malliavinTailCLM n x)).hasFDerivAt.comp
    x (malliavinTailCLM n).hasFDerivAt
  have hfd' : fderiv ℝ (malliavinTailLift f) x =
      (fderiv ℝ f (malliavinTailCLM n x)).comp (malliavinTailCLM n) := by
    change fderiv ℝ (fun y => f (malliavinTailCLM n y)) x = _
    exact hfd.fderiv
  unfold coordinateDerivative
  rw [hfd', ContinuousLinearMap.comp_apply, malliavinTailCLM_single_succ]

theorem gaussian_cylindrical_ibp_duality
    {P : Measure Ω} {n : ℕ}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {h : Fin n → SpaceTime → ℝ} {k : SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ}
    {Y : Ω → Fin (n + 1) → ℝ} {B A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsCentredGaussianVector P Y B)
    (hAsymm : A.IsSymm) (hAsq : A * A = B)
    (hlaw : P.map Y = (standardGaussianMeasure (n + 1)).map
      (Matrix.mulVecLin A))
    (hcont_f : ContDiff ℝ 1 f)
    (_hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_tail : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + 1) → ℝ,
        |malliavinTailLift f x| + ‖fderiv ℝ (malliavinTailLift f) x‖ ≤
          K * (1 + ‖x‖) ^ M)
    (hgrowth_g : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin (n + 1) → ℝ,
        |malliavinTailLift f (Matrix.mulVec A z)| +
          ‖fderiv ℝ (fun y => malliavinTailLift f (Matrix.mulVec A y)) z‖ ≤
            K * (1 + ‖z‖) ^ M)
    (hint_g : Integrable (fun ω => malliavinTailLift f (Y ω)) P)
    (hint_deriv_g : ∀ i, Integrable
      (fun ω => coordinateDerivative (malliavinTailLift f) i (Y ω)) P)
    (hint_x_g : ∀ i, Integrable
      (fun ω => Y ω i * malliavinTailLift f (Y ω)) P)
    (hint_g_std : Integrable
      (fun z : Fin (n + 1) → ℝ => malliavinTailLift f (Matrix.mulVec A z))
        (standardGaussianMeasure (n + 1)))
    (hint_deriv_g_std : ∀ i, Integrable
      (fun z : Fin (n + 1) → ℝ =>
        coordinateDerivative (malliavinTailLift f) i (Matrix.mulVec A z))
        (standardGaussianMeasure (n + 1)))
    (hint_x_g_std : ∀ i, Integrable
      (fun z : Fin (n + 1) → ℝ =>
        z i * malliavinTailLift f (Matrix.mulVec A z))
        (standardGaussianMeasure (n + 1)))
    (hint_g_density : Integrable
      (fun z : Fin (n + 1) → ℝ =>
        malliavinTailLift f (Matrix.mulVec A z) * standardGaussianDensityReal z) volume)
    (hint_deriv_g_density : ∀ i, Integrable
      (fun z : Fin (n + 1) → ℝ =>
        coordinateDerivative (malliavinTailLift f) i (Matrix.mulVec A z) *
          standardGaussianDensityReal z) volume)
    (hint_x_g_density : ∀ i, Integrable
      (fun z : Fin (n + 1) → ℝ =>
        z i * malliavinTailLift f (Matrix.mulVec A z) *
          standardGaussianDensityReal z) volume)
    (hY_zero : ∀ ω, Y ω 0 = W k ω)
    (hY_succ : ∀ (ω : Ω) (i : Fin n), Y ω i.succ = W (h i) ω)
    (hB : ∀ i : Fin n, B 0 i.succ = ∫ z, k z * h i z) :
    ∫ ω, f (fun i => W (h i) ω) * W k ω ∂P =
      ∑ i, (∫ ω, coordinateDerivative f i (fun j => W (h j) ω) ∂P) *
        (∫ z, h i z * k z) := by
  have hparts := gaussian_vector_integration_by_parts_of_standard_representation
    hY hAsymm hAsq hlaw (hcont_f.comp (malliavinTailCLM n).contDiff)
    (by
      exact hgrowth_tail)
    hgrowth_g hint_g hint_deriv_g hint_x_g hint_g_std hint_deriv_g_std hint_x_g_std
    hint_g_density hint_deriv_g_density hint_x_g_density 0
  change
    ∫ ω, Y ω 0 * malliavinTailLift f (Y ω) ∂P =
      ∑ i, B 0 i * ∫ ω, coordinateDerivative (malliavinTailLift f) i (Y ω) ∂P at hparts
  have hzero : ∫ ω, coordinateDerivative (malliavinTailLift f) 0 (Y ω) ∂P = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with ω
    exact coordinateDerivative_malliavinTailLift_zero hcont_f (Y ω)
  have hsucc (i : Fin n) :
      ∫ ω, coordinateDerivative (malliavinTailLift f) i.succ (Y ω) ∂P =
        ∫ ω, coordinateDerivative f i (fun j => W (h j) ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [coordinateDerivative_malliavinTailLift_succ hcont_f]
    congr 1
    funext j
    rw [malliavinTailCLM_apply, hY_succ]
  have hleft :
      ∫ ω, Y ω 0 * malliavinTailLift f (Y ω) ∂P =
        ∫ ω, f (fun i => W (h i) ω) * W k ω ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hY_zero, malliavinTailLift_apply]
    have htail : (fun i => Y ω i.succ) = (fun i => W (h i) ω) := by
      funext i
      rw [hY_succ]
    rw [htail]
    ring
  rw [hleft] at hparts
  rw [Fin.sum_univ_succ, hzero] at hparts
  simp only [mul_zero, zero_add] at hparts
  have hsum :
      (∑ i : Fin n, B 0 i.succ *
        ∫ ω, coordinateDerivative (malliavinTailLift f) i.succ (Y ω) ∂P) =
      ∑ i : Fin n,
        (∫ ω, coordinateDerivative f i (fun j => W (h j) ω) ∂P) *
          (∫ z, h i z * k z) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hB i, hsucc i]
    have hkh : (∫ z, k z * h i z) = ∫ z, h i z * k z := by
      congr 1
      funext z
      ring
    rw [hkh]
    ring
  rw [hsum] at hparts
  exact hparts

end RegularityStructures

end
