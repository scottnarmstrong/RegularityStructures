/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.SpectralGap
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Covariance energy of a centred Gaussian vector

The identity proved here is the algebraic covariance part of the finite-dimensional Gaussian
spectral-gap argument.  It uses the strengthened a.e.-measurability clause in
`IsCentredGaussianVector` from `WhiteNoise.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

set_option linter.style.haveILetI false in
theorem centredGaussian_linear_variance_eq_covarianceEnergy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (a : Fin n → ℝ) :
    Var[fun ω => ∑ i, a i * X ω i; P] = covarianceEnergy C a := by
  haveI : IsGaussian (P.map X) := hX.2.1
  have hprob : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    calc
      P Set.univ = (P.map X) Set.univ := by
        rw [Measure.map_apply_of_aemeasurable hX.1 MeasurableSet.univ]
        simp
      _ = 1 := measure_univ
  haveI : IsProbabilityMeasure P := hprob
  have hXlp : MemLp X 2 P := by
    have hmap : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) 2 (P.map X) :=
      IsGaussian.memLp_id (P.map X) 2 (by norm_num)
    simpa only [Function.id_comp] using hmap.comp_of_map hX.1
  have hcoord (i : Fin n) : MemLp (fun ω => X ω i) 2 P := by
    let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have h := hXlp.continuousLinearMap_comp L
    simpa [L, Function.comp_def] using h
  have hcov (i j : Fin n) : cov[fun ω => X ω i, fun ω => X ω j; P] = C i j := by
    rw [covariance_eq_sub (hcoord i) (hcoord j)]
    simp only [Pi.mul_apply]
    rw [hX.2.2.2 i j, hX.2.2.1 i, hX.2.2.1 j]
    simp
  let Y : Ω → ℝ := fun ω => ∑ i, a i * X ω i
  have hY : MemLp Y 2 P := by
    dsimp [Y]
    apply memLp_finsetSum
    intro i hi
    exact (hcoord i).const_mul (a i)
  calc
    Var[Y; P] = cov[Y, Y; P] := (covariance_self hY.aemeasurable).symm
    _ = ∑ i, ∑ j, cov[fun ω => a i * X ω i, fun ω => a j * X ω j; P] := by
      simpa [Y] using
        (covariance_fun_sum_fun_sum
          (X := fun i ω => a i * X ω i) (Y := fun j ω => a j * X ω j)
          (fun i => (hcoord i).const_mul (a i))
          (fun j => (hcoord j).const_mul (a j)))
    _ = covarianceEnergy C a := by
      simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
      unfold covarianceEnergy
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

end RegularityStructures

end
