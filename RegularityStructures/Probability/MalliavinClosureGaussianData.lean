/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPolynomial
public import RegularityStructures.Probability.Poincare
public import RegularityStructures.Probability.StandardGaussianIBP
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability against the finite-dimensional Gaussian density

The finite-dimensional IBP theorem records Lebesgue-density integrability separately from
integrability under the standard Gaussian law.  This file supplies that conversion for arbitrary
`L¹` functions, using the explicit product density of the standard Gaussian law.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

private lemma malliavin_standardGaussianDensity_toReal {n : ℕ}
    (x : Fin n → ℝ) :
    (standardGaussianDensity x).toReal = standardGaussianDensityReal x := by
  simp [standardGaussianDensity, standardGaussianDensityReal]

private lemma malliavin_measurable_standardGaussianDensity {n : ℕ} :
    Measurable (standardGaussianDensity (n := n)) := by
  unfold standardGaussianDensity
  fun_prop

private lemma malliavin_standardGaussianMeasure_eq_withDensity (n : ℕ) :
    standardGaussianMeasure n =
      (volume : Measure (Fin n → ℝ)).withDensity standardGaussianDensity := by
  classical
  refine Measure.pi_eq (μ := fun _ : Fin n => gaussianReal 0 1) (fun s hs => ?_)
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hset, ← lintegral_indicator hset]
  have hprod : Integrable
      (fun x : Fin n → ℝ => ∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i))
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
    apply Integrable.fintype_prod
    intro i
    exact (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hnonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => (volume : Measure ℝ))]
      (fun x : Fin n → ℝ => ∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i)) :=
    Filter.Eventually.of_forall (fun x => Finset.prod_nonneg fun i _ => by
      by_cases hx : x i ∈ s i
      · rw [Set.indicator_of_mem hx]
        exact gaussianPDFReal_nonneg 0 1 _
      · rw [Set.indicator_of_notMem hx])
  have hpoint :
      (Set.univ.pi s).indicator standardGaussianDensity =
        (fun x : Fin n → ℝ => ENNReal.ofReal
          (∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i))) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · have hxi : ∀ i, x i ∈ s i := by simpa using hx
      simp only [Set.indicator_of_mem hx, standardGaussianDensity]
      rw [ENNReal.ofReal_prod_of_nonneg]
      · congr 1
        funext i
        simp [Set.indicator_of_mem (hxi i), gaussianPDF]
      · intro i hi
        simp [Set.indicator_of_mem (hxi i), gaussianPDFReal_nonneg]
    · obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        have hnot : ¬ ∀ i, x i ∈ s i := by
          intro hall
          exact hx (Set.mem_pi.2 (fun i _ => hall i))
        exact not_forall.mp hnot
      rw [Set.indicator_of_notMem hx]
      have hzero : (s i).indicator (gaussianPDFReal 0 1) (x i) = 0 :=
        Set.indicator_of_notMem hi _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
      simp
  rw [hpoint]
  change (∫⁻ x : Fin n → ℝ, ENNReal.ofReal
      (∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i)) ∂
        (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hprod hnonneg]
  · rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_indicator (hs _), gaussianReal_apply_eq_integral 0 one_ne_zero]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    intro i hi
    exact integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x

theorem malliavin_integrable_standardGaussian_density {n : ℕ}
    {g : (Fin n → ℝ) → ℝ} (hg : Integrable g (standardGaussianMeasure n)) :
    Integrable (fun x => g x * standardGaussianDensityReal x)
      (volume : Measure (Fin n → ℝ)) := by
  have htop : ∀ᵐ x : Fin n → ℝ ∂(volume : Measure (Fin n → ℝ)),
      standardGaussianDensity x < ⊤ :=
    Filter.Eventually.of_forall (fun x => by
      exact ENNReal.prod_lt_top (fun k hk => gaussianPDF_lt_top))
  have h := hg
  rw [malliavin_standardGaussianMeasure_eq_withDensity] at h
  have h' := (integrable_withDensity_iff_integrable_smul'
    malliavin_measurable_standardGaussianDensity htop).1 h
  refine h'.congr ?_
  filter_upwards [] with x
  rw [malliavin_standardGaussianDensity_toReal]
  simp [smul_eq_mul]
  ring

end RegularityStructures

end
