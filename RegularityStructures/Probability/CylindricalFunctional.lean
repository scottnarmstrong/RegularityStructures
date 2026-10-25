/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.SpectralGap
public import RegularityStructures.Probability.WhiteNoise
public import RegularityStructures.Probability.Poincare
public import RegularityStructures.Probability.StandardGaussianIBP
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Covariance

/-!
# Cylindrical functionals of white noise

`cylindricalFunctional W h f = f(W h₁, …, W hₙ)` and its derivative `cylindricalDerivative`; the
variance and the derivative energy, and the reduction of the spectral gap for cylindrical
functionals to the finite-dimensional Gaussian Poincaré inequality
(`cylindrical_spectral_gap_reduction`).

Source: [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

/-- A cylindrical function of a finite family of random coordinates. -/
def cylindricalFunctional {Ω : Type*} {n : ℕ} (W : (SpaceTime → ℝ) → Ω → ℝ)
    (h : Fin n → SpaceTime → ℝ) (f : (Fin n → ℝ) → ℝ) : Ω → ℝ :=
  fun ω => f (fun i => W (h i) ω)

/-- The literal cylindrical/Malliavin derivative in the white-noise variable. -/
def cylindricalDerivative {Ω : Type*} {n : ℕ} (W : (SpaceTime → ℝ) → Ω → ℝ)
    (h : Fin n → SpaceTime → ℝ) (f : (Fin n → ℝ) → ℝ) (ω : Ω) (z : SpaceTime) : ℝ :=
  ∑ i, coordinateDerivative f i (fun j => W (h j) ω) * h i z

theorem cylindricalFunctional_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W) (hmem : ∀ i, MemLp (h i) 2)
    (hcont : ContDiff ℝ 1 f) :
    Measurable (cylindricalFunctional W h f) := by
  have hcoords : Measurable (fun ω i => W (h i) ω) := by
    rw [measurable_pi_iff]
    intro i
    exact hW.1 (h i) (hmem i)
  exact hcont.continuous.measurable.comp hcoords

theorem cylindrical_variance_eq_variance_map {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W) (hmem : ∀ i, MemLp (h i) 2)
    (hcont : ContDiff ℝ 1 f) :
    Var[cylindricalFunctional W h f; P] =
      Var[f; P.map (fun ω i => W (h i) ω)] := by
  have hX : AEMeasurable (fun ω i => W (h i) ω) P :=
    (hW.2 n h hmem).1
  rw [variance_map hcont.continuous.measurable.aemeasurable hX]
  rfl

theorem cylindrical_energy_eq_integral_sq {n : ℕ} {a : Fin n → ℝ}
    {h : Fin n → SpaceTime → ℝ} (hmem : ∀ i, MemLp (h i) 2) :
    ∫ z, (∑ i, a i * h i z) ^ 2 =
      covarianceEnergy (fun i j => ∫ z, h i z * h j z) a := by
  have hsum :
      (fun z => (∑ i, a i * h i z) ^ 2) =
        (fun z => ∑ i, ∑ j, (a i * h i z) * (a j * h j z)) := by
    funext z
    simp only [pow_two, Finset.sum_mul_sum]
  rw [hsum]
  have hpair : ∀ i j, Integrable (fun z => (a i * h i z) * (a j * h j z)) := by
    intro i j
    exact memLp_one_iff_integrable.1
      (((hmem i).const_mul (a i)).mul ((hmem j).const_mul (a j)))
  have hinner : ∀ i, Integrable (fun z => ∑ j, (a i * h i z) * (a j * h j z)) := by
    intro i
    apply integrable_finsetSum
    intro j hj
    exact hpair i j
  have houter := integral_finsetSum (Finset.univ : Finset (Fin n))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hinner i)
  rw [houter]
  have hinner_eq (i : Fin n) :
      ∫ z, ∑ j, (a i * h i z) * (a j * h j z) =
        ∑ j, ∫ z, (a i * h i z) * (a j * h j z) :=
    integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpair i j)
  simp_rw [hinner_eq]
  have hpair_eq (i j : Fin n) :
      ∫ z, (a i * h i z) * (a j * h j z) =
        a i * (∫ z, h i z * h j z) * a j := by
    have hfun :
        (fun z => (a i * h i z) * (a j * h j z)) =
          (fun z => a i * (h i z * h j z) * a j) := by
      funext z
      ring
    rw [hfun, integral_mul_const, integral_const_mul]
  simp_rw [hpair_eq]
  unfold covarianceEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem cylindrical_spectral_gap_reduction {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W) (hmem : ∀ i, MemLp (h i) 2)
    (hcont : ContDiff ℝ 1 f)
    (hcoord : Var[f; P.map (fun ω i => W (h i) ω)] ≤
      ∫ ω, covarianceEnergy (fun i j => ∫ z, h i z * h j z)
        (fun i => coordinateDerivative f i (fun j => W (h j) ω)) ∂P) :
    Var[cylindricalFunctional W h f; P] ≤
      ∫ ω, (∫ z, (cylindricalDerivative W h f ω z) ^ 2
        ∂(volume : Measure SpaceTime)) ∂P := by
  rw [cylindrical_variance_eq_variance_map hW hmem hcont]
  calc
    Var[f; P.map (fun ω i => W (h i) ω)] ≤
        ∫ ω, covarianceEnergy (fun i j => ∫ z, h i z * h j z)
          (fun i => coordinateDerivative f i (fun j => W (h j) ω)) ∂P := hcoord
    _ = ∫ ω, (∫ z, (cylindricalDerivative W h f ω z) ^ 2
      ∂(volume : Measure SpaceTime)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simpa [cylindricalDerivative] using
        (cylindrical_energy_eq_integral_sq
          (a := fun i => coordinateDerivative f i (fun j => W (h j) ω)) hmem).symm

end RegularityStructures

end
