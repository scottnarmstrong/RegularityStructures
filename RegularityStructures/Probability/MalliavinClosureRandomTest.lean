/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureDuality
public import RegularityStructures.Probability.MalliavinClosureProductLp
public import RegularityStructures.Probability.MalliavinClosureCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-rank random test fields

This file isolates the algebraic part of the Malliavin duality calculation.  The only Gaussian
input is the displayed coordinate integration-by-parts identity; the remaining conclusion is the
pairing identity for the random test field `u(W h) k`.  This separation keeps every integrability
requirement explicit while avoiding any second derivative assumption on the coefficient `u`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem malliavin_random_test_duality_of_ibp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} {n : ℕ}
    {h : Fin n → SpaceTime → ℝ} {f u : (Fin n → ℝ) → ℝ} {k : SpaceTime → ℝ}
    (hmem_h : ∀ i, MemLp (h i) 2)
    (hmem_k : MemLp k 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_u : ContDiff ℝ 1 u)
    (hgrad : ∀ i, Integrable
      (fun ω => coordinateDerivative f i (fun j => W (h j) ω) *
        u (fun j => W (h j) ω)) P)
    (hfdu : ∀ i, Integrable
      (fun ω => f (fun j => W (h j) ω) *
        coordinateDerivative u i (fun j => W (h j) ω)) P)
    (hfuW : Integrable
      (fun ω => (f (fun j => W (h j) ω) * u (fun j => W (h j) ω)) * W k ω) P)
    (hIBP : ∫ ω,
        (f (fun j => W (h j) ω) * u (fun j => W (h j) ω)) * W k ω ∂P =
      ∑ i, (∫ ω, coordinateDerivative (fun x => f x * u x) i
          (fun j => W (h j) ω) ∂P) * ∫ z, h i z * k z) :
    ∫ p, cylindricalDerivative W h f p.1 p.2 *
        (u (fun i => W (h i) p.1) * k p.2) ∂(whiteNoiseDerivativeMeasure P) =
      ∫ ω, f (fun i => W (h i) ω) *
        (u (fun i => W (h i) ω) * W k ω -
          ∑ i, (∫ z, h i z * k z) *
            coordinateDerivative u i (fun j => W (h j) ω)) ∂P := by
  let X : Ω → Fin n → ℝ := fun ω i => W (h i) ω
  let uX : Ω → ℝ := fun ω => u (X ω)
  let fX : Ω → ℝ := fun ω => f (X ω)
  have hprod_hk (i : Fin n) : Integrable (fun z => h i z * k z) := by
    exact (hmem_h i).integrable_mul hmem_k
  have hprod_grad (i : Fin n) : Integrable
      (fun p : Ω × SpaceTime =>
        (coordinateDerivative f i (X p.1) * uX p.1) * (h i p.2 * k p.2))
      (whiteNoiseDerivativeMeasure P) := by
    exact (hgrad i).mul_prod (hprod_hk i)
  have hleft :
      ∫ p, cylindricalDerivative W h f p.1 p.2 * (uX p.1 * k p.2)
          ∂(whiteNoiseDerivativeMeasure P) =
        ∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
          ∫ z, h i z * k z := by
    rw [show (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2 * (uX p.1 * k p.2)) =
      (fun p => ∑ i, (coordinateDerivative f i (X p.1) * uX p.1) *
        (h i p.2 * k p.2)) by
        funext p
        unfold cylindricalDerivative
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      simpa [whiteNoiseDerivativeMeasure, X, uX, mul_assoc] using
        (integral_prod_mul (μ := P) (ν := (volume : Measure SpaceTime))
          (fun ω => coordinateDerivative f i (X ω) * uX ω)
          (fun z => h i z * k z))
    · intro i hi
      exact hprod_grad i
  have hderiv (i : Fin n) (ω : Ω) :
      coordinateDerivative (fun x => f x * u x) i (X ω) =
        coordinateDerivative f i (X ω) * uX ω +
          fX ω * coordinateDerivative u i (X ω) := by
    exact coordinateDerivative_mul hcont_f hcont_u i (X ω)
  have hIBP' :
      ∫ ω, (fX ω * uX ω) * W k ω ∂P =
        ∑ i, ((∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) +
          ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P) *
          ∫ z, h i z * k z := by
    rw [hIBP]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun ω => hderiv i ω))]
    rw [integral_add (hgrad i) (hfdu i)]
  have hright_integrable : Integrable
      (fun ω => fX ω *
        (uX ω * W k ω - ∑ i, (∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) P := by
    have hfirst : Integrable (fun ω => fX ω * uX ω * W k ω) P := by
      simpa [mul_assoc] using hfuW
    have hsecond (i : Fin n) : Integrable
        (fun ω => fX ω * ((∫ z, h i z * k z) * coordinateDerivative u i (X ω))) P := by
      have hi := (hfdu i).const_mul (∫ z, h i z * k z)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hi
    have hsum : Integrable
        (fun ω => ∑ i, fX ω * ((∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) P := by
      apply integrable_finsetSum
      intro i hi
      exact hsecond i
    have heq : (fun ω => fX ω *
        (uX ω * W k ω - ∑ i, (∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) =
      (fun ω => fX ω * uX ω * W k ω -
        ∑ i, fX ω * ((∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) := by
      funext ω
      rw [mul_sub, Finset.mul_sum]
      ring
    rw [heq]
    exact hfirst.sub hsum
  have hright :
      ∫ ω, fX ω *
        (uX ω * W k ω - ∑ i, (∫ z, h i z * k z) *
          coordinateDerivative u i (X ω)) ∂P =
      (∫ ω, fX ω * uX ω * W k ω ∂P) -
        ∑ i, (∫ z, h i z * k z) *
          ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P := by
    have hfirst : Integrable (fun ω => fX ω * uX ω * W k ω) P := by
      simpa [mul_assoc] using hfuW
    have hsecond (i : Fin n) : Integrable
        (fun ω => fX ω * ((∫ z, h i z * k z) * coordinateDerivative u i (X ω))) P := by
      have hi := (hfdu i).const_mul (∫ z, h i z * k z)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hi
    have heq : (fun ω => fX ω *
        (uX ω * W k ω - ∑ i, (∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) =
      (fun ω => fX ω * uX ω * W k ω -
        ∑ i, fX ω * ((∫ z, h i z * k z) *
          coordinateDerivative u i (X ω))) := by
      funext ω
      rw [mul_sub, Finset.mul_sum]
      ring
    rw [heq, integral_sub hfirst]
    · rw [integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : (fun a : Ω => fX a *
            ((∫ z, h i z * k z) * coordinateDerivative u i (X a))) =
            (fun a => (∫ z, h i z * k z) *
              (fX a * coordinateDerivative u i (X a))) := by
          funext a
          ring
        rw [hi', integral_const_mul]
      · intro i hi
        exact hsecond i
    · apply integrable_finsetSum
      intro i hi
      exact hsecond i
  calc
    ∫ p, cylindricalDerivative W h f p.1 p.2 * (uX p.1 * k p.2)
        ∂(whiteNoiseDerivativeMeasure P) =
      ∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
        ∫ z, h i z * k z := hleft
    _ = (∫ ω, fX ω * uX ω * W k ω ∂P) -
        ∑ i, (∫ z, h i z * k z) *
          ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P := by
      rw [hIBP']
      have hsum :
          (∑ i, ((∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) +
            ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P) *
            (∫ z, h i z * k z)) =
          (∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
            (∫ z, h i z * k z)) +
          ∑ i, (∫ z, h i z * k z) *
            ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P := by
        calc
          _ = ∑ i, ((∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
              (∫ z, h i z * k z) +
              (∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P) *
                (∫ z, h i z * k z)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = (∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
              (∫ z, h i z * k z)) +
              ∑ i, (∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P) *
                (∫ z, h i z * k z) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
              (∫ z, h i z * k z)) +
              ∑ i, (∫ z, h i z * k z) *
                ∫ ω, fX ω * coordinateDerivative u i (X ω) ∂P := by
                apply congrArg (fun q =>
                  (∑ i, (∫ ω, coordinateDerivative f i (X ω) * uX ω ∂P) *
                    (∫ z, h i z * k z)) + q)
                apply Finset.sum_congr rfl
                intro i hi
                ring
      rw [hsum]
      ring
    _ = ∫ ω, fX ω *
        (uX ω * W k ω - ∑ i, (∫ z, h i z * k z) *
          coordinateDerivative u i (X ω)) ∂P := hright.symm

end RegularityStructures

end
