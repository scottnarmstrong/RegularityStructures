/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureTestDensity
public import RegularityStructures.Probability.MalliavinClosureProductLp
public import RegularityStructures.Probability.MalliavinClosureGrowth
public import RegularityStructures.Probability.MalliavinClosureCore

set_option linter.style.haveILetI false

/-!
# Smooth finite-rank test fields

The derivative space is an `L²` space on `Ω × SpaceTime`.  Its useful test fields are finite sums
of products `u(W(h₁), ..., W(hₙ)) k`, with compactly supported smooth coefficient functions.  This
file defines that concrete test set and proves that every explicitly cylindrical derivative is in
its closure.  The approximation is finite-dimensional Gaussian density followed by the exact
product-measure `L²` factorisation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

def malliavinSmoothTestFieldSet (P : Measure Ω)
    (W : (SpaceTime → ℝ) → Ω → ℝ) :
    Set (Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) :=
  {V | ∃ (n m : ℕ) (h : Fin n → SpaceTime → ℝ)
      (u : Fin m → (Fin n → ℝ) → ℝ) (k : Fin m → SpaceTime → ℝ),
      (∀ i, MemLp (h i) 2) ∧
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u j)) ∧
      (∀ j, HasCompactSupport (u j)) ∧
      (∀ j, MemLp (fun ω => u j (fun i => W (h i) ω)) 2 P) ∧
      (∀ j, MemLp (k j) 2) ∧
      ∃ hsum : MemLp (fun p : Ω × SpaceTime =>
        ∑ j, u j (fun i => W (h i) p.1) * k j p.2) 2
        (whiteNoiseDerivativeMeasure P),
      V = (MemLp.toLp
        (fun p : Ω × SpaceTime =>
          ∑ j, u j (fun i => W (h i) p.1) * k j p.2)
        hsum)}

private lemma malliavin_coordinateDerivative_bound_of_growth {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} {N : ℕ} (_hC : 0 ≤ C)
    (hgrowth : ∀ x : Fin n → ℝ,
      |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (i : Fin n) (x : Fin n → ℝ) :
    |coordinateDerivative f i x| ≤ C * (1 + ‖x‖) ^ N := by
  have hnorm : ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (Pi.single i 1)
    have hs : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
      classical
      rw [Pi.norm_single]
      simp
    simpa [hs] using h
  have hsum : ‖fderiv ℝ f x‖ ≤ |f x| + ‖fderiv ℝ f x‖ :=
    le_add_of_nonneg_left (abs_nonneg _)
  have h := hnorm.trans (hsum.trans (hgrowth x))
  simpa [coordinateDerivative, Real.norm_eq_abs] using h

private lemma malliavin_coordinateDerivative_continuous {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hcont : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x => coordinateDerivative f i x) := by
  have h := hcont.continuous_fderiv_apply one_ne_zero
  simpa [coordinateDerivative, Function.comp_def] using h.comp
    (by fun_prop : Continuous (fun x : Fin n → ℝ => (x, Pi.single i 1)))

private lemma malliavin_derivative_term_memLp
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} {n : ℕ}
    {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hXg : IsCentredGaussianVector P (fun ω i => W (h i) ω)
      (fun i j => ∫ z, h i z * h j z))
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (i : Fin n) :
    MemLp (fun ω => coordinateDerivative f i (fun j => W (h j) ω)) 2 P := by
  let X : Ω → Fin n → ℝ := fun ω j => W (h j) ω
  letI : IsGaussian (P.map X) := hXg.2.1
  rcases hgrowth with ⟨C, N, hC, hgrowth⟩
  have hbound : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |coordinateDerivative f i x| ≤ C * (1 + ‖x‖) ^ N :=
    ⟨C, N, hC, malliavin_coordinateDerivative_bound_of_growth hC hgrowth i⟩
  have hmap := memLp_of_polynomial_bound_gaussian
    ((malliavin_coordinateDerivative_continuous hcont i).measurable.aestronglyMeasurable
      (μ := P.map X)) hbound
  have hpull := hmap.comp_of_map hXg.1
  simpa [X, Function.comp_def] using hpull

theorem malliavin_cylindricalDerivative_mem_closure_smooth_test_fields
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem_h : ∀ i, MemLp (h i) 2)
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hD : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P)) :
    hD.toLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) ∈
      closure (malliavinSmoothTestFieldSet P W) := by
  let X : Ω → Fin n → ℝ := fun ω i => W (h i) ω
  have hXg : IsCentredGaussianVector P X
      (fun i j => ∫ z, h i z * h j z) := by
    simpa [X] using hW.2 n h hmem_h
  have hcoef (i : Fin n) :
      MemLp (fun ω => coordinateDerivative f i (X ω)) 2 P := by
    exact malliavin_derivative_term_memLp hXg hcont hgrowth i
  have hcoef' (i : Fin n) :
      MemLp (coordinateDerivative f i) 2 (P.map X) := by
    letI : IsGaussian (P.map X) := hXg.2.1
    rcases hgrowth with ⟨C, N, hC, hg⟩
    exact memLp_of_polynomial_bound_gaussian
      ((malliavin_coordinateDerivative_continuous hcont i).measurable.aestronglyMeasurable)
      ⟨C, N, hC, malliavin_coordinateDerivative_bound_of_growth hC hg i⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hdenom (i : Fin n) :
      0 < (2 : ℝ) * ((n : ℝ) + 1) *
        (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hi : 0 ≤ (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal :=
      ENNReal.toReal_nonneg
    positivity
  have hex (i : Fin n) : ∃ u : (Fin n → ℝ) → ℝ,
      HasCompactSupport u ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      MemLp (fun ω => u (X ω)) 2 P ∧
      eLpNorm (fun ω => coordinateDerivative f i (X ω) - u (X ω)) 2 P <
        ENNReal.ofReal
          (ε / ((2 : ℝ) * ((n : ℝ) + 1) *
            (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal))) := by
    exact malliavin_compact_smooth_pullback_approx hXg.1 (hcoef' i)
      (div_pos hε (hdenom i))
  choose u hu_support hu_cont huP huerr using hex
  have hterm (i : Fin n) :
      MemLp (fun p : Ω × SpaceTime => u i (X p.1) * h i p.2) 2
        (whiteNoiseDerivativeMeasure P) := by
    exact memLp_prod_mul_of_memLp_two (huP i) (hmem_h i)
  have hsum : MemLp (fun p : Ω × SpaceTime =>
      ∑ i, u i (X p.1) * h i p.2) 2 (whiteNoiseDerivativeMeasure P) := by
    simpa using (memLp_finsetSum (Finset.univ : Finset (Fin n))
      (fun i hi => hterm i))
  let V : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) := hsum.toLp
    (fun p : Ω × SpaceTime => ∑ i, u i (X p.1) * h i p.2)
  have hVmem : V ∈ malliavinSmoothTestFieldSet P W := by
    refine ⟨n, n, h, (fun i => u i), h, hmem_h, hu_cont, hu_support, ?_,
      hmem_h, ?_, ?_⟩
    · intro i
      simpa [X] using huP i
    · simpa [X] using hsum
    · rfl
  refine ⟨V, hVmem, ?_⟩
  have hdi (i : Fin n) :
      MemLp (fun p : Ω × SpaceTime =>
        coordinateDerivative f i (X p.1) * h i p.2) 2
          (whiteNoiseDerivativeMeasure P) :=
    memLp_prod_mul_of_memLp_two (hcoef i) (hmem_h i)
  have hdist_i (i : Fin n) :
      dist ((hdi i).toLp (fun p : Ω × SpaceTime =>
        coordinateDerivative f i (X p.1) * h i p.2))
        ((hterm i).toLp (fun p : Ω × SpaceTime => u i (X p.1) * h i p.2)) ≤
        ε / ((2 : ℝ) * ((n : ℝ) + 1)) := by
    rw [Lp.dist_def]
    have heq : eLpNorm
        ((fun p : Ω × SpaceTime => coordinateDerivative f i (X p.1) * h i p.2) -
          fun p => u i (X p.1) * h i p.2) 2 (whiteNoiseDerivativeMeasure P) =
        eLpNorm (fun p : Ω × SpaceTime =>
          (coordinateDerivative f i (X p.1) - u i (X p.1)) * h i p.2) 2
          (whiteNoiseDerivativeMeasure P) := by
      apply eLpNorm_congr_ae
      filter_upwards [] with p
      simp only [Pi.sub_apply]
      ring
    rw [eLpNorm_congr_ae ((hdi i).coeFn_toLp.sub (hterm i).coeFn_toLp)]
    rw [heq]
    have hprod : eLpNorm (fun p : Ω × SpaceTime =>
        (coordinateDerivative f i (X p.1) - u i (X p.1)) * h i p.2) 2
          (whiteNoiseDerivativeMeasure P) =
        eLpNorm (fun ω => coordinateDerivative f i (X ω) - u i (X ω)) 2 P *
          eLpNorm (h i) 2 (volume : Measure SpaceTime) := by
      have hp := eLpNorm_prod_mul_eq ((hcoef i).sub (huP i)) (hmem_h i)
      have hfun : (fun ω => coordinateDerivative f i (X ω) - u i (X ω)) =
          (fun ω => coordinateDerivative f i (X ω)) - (fun ω => u i (X ω)) := by
        funext ω
        rfl
      rw [← hfun] at hp
      exact hp
    rw [hprod]
    have herr := huerr i
    have herr_real :
        (eLpNorm (fun ω => coordinateDerivative f i (X ω) - u i (X ω)) 2 P).toReal <
          ε / ((2 : ℝ) * ((n : ℝ) + 1) *
            (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal)) := by
      exact ENNReal.toReal_lt_of_lt_ofReal herr
    rw [ENNReal.toReal_mul]
    have hnonneg : 0 ≤ (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal :=
      ENNReal.toReal_nonneg
    have hbound :
        ε / ((2 : ℝ) * ((n : ℝ) + 1) *
          (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal)) *
          (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal ≤
        ε / ((2 : ℝ) * ((n : ℝ) + 1)) := by
      have hpos : 0 < (2 : ℝ) * ((n : ℝ) + 1) := by positivity
      have hden : 0 < 1 +
          (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal := by linarith
      have hfrac :
          (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal /
            (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal) ≤ 1 := by
        exact (div_le_iff₀ hden).2 (by linarith)
      calc
        _ = (ε / ((2 : ℝ) * ((n : ℝ) + 1))) *
            ((eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal /
              (1 + (eLpNorm (h i) 2 (volume : Measure SpaceTime)).toReal)) := by
          field_simp
        _ ≤ _ := by
          calc
            _ ≤ (ε / ((2 : ℝ) * ((n : ℝ) + 1))) * 1 :=
              mul_le_mul_of_nonneg_left hfrac (by positivity :
                0 ≤ ε / ((2 : ℝ) * ((n : ℝ) + 1)))
            _ = _ := by ring
    exact (mul_le_mul_of_nonneg_right (le_of_lt herr_real) hnonneg).trans hbound
  have hDsum : hD.toLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) =
      ∑ i, (hdi i).toLp (fun p : Ω × SpaceTime =>
        coordinateDerivative f i (X p.1) * h i p.2) := by
    apply Lp.ext
    have hsum' : (⇑(∑ i, (hdi i).toLp (fun p : Ω × SpaceTime =>
        coordinateDerivative f i (X p.1) * h i p.2)) : Ω × SpaceTime → ℝ) =ᵐ[
          whiteNoiseDerivativeMeasure P] fun p =>
        ∑ i, ((hdi i).toLp (fun p : Ω × SpaceTime =>
          coordinateDerivative f i (X p.1) * h i p.2)) p := by
      convert Lp.coeFn_finsetSum (Finset.univ : Finset (Fin n))
        (fun i => (hdi i).toLp (fun p : Ω × SpaceTime =>
          coordinateDerivative f i (X p.1) * h i p.2)) using 1
      funext p
      simp only [Finset.sum_apply]
    have hdi_all : ∀ᵐ p : Ω × SpaceTime ∂whiteNoiseDerivativeMeasure P,
        ∀ i, ((hdi i).toLp (fun p : Ω × SpaceTime =>
          coordinateDerivative f i (X p.1) * h i p.2)) p =
          coordinateDerivative f i (X p.1) * h i p.2 :=
      ae_all_iff.2 (fun i => (hdi i).coeFn_toLp)
    filter_upwards [hD.coeFn_toLp, hsum', hdi_all] with p hp hs hall
    rw [hp]
    unfold cylindricalDerivative
    rw [hs]
    apply Finset.sum_congr rfl
    intro i hi
    simpa [X] using (hall i).symm
  have hVsum : V = ∑ i, (hterm i).toLp (fun p : Ω × SpaceTime =>
      u i (X p.1) * h i p.2) := by
    apply Lp.ext
    have hsum' : (⇑(∑ i, (hterm i).toLp (fun p : Ω × SpaceTime =>
        u i (X p.1) * h i p.2)) : Ω × SpaceTime → ℝ) =ᵐ[
          whiteNoiseDerivativeMeasure P] fun p =>
        ∑ i, ((hterm i).toLp (fun p : Ω × SpaceTime =>
          u i (X p.1) * h i p.2)) p := by
      convert Lp.coeFn_finsetSum (Finset.univ : Finset (Fin n))
        (fun i => (hterm i).toLp (fun p : Ω × SpaceTime =>
          u i (X p.1) * h i p.2)) using 1
      funext p
      simp only [Finset.sum_apply]
    have hterm_all : ∀ᵐ p : Ω × SpaceTime ∂whiteNoiseDerivativeMeasure P,
        ∀ i, ((hterm i).toLp (fun p : Ω × SpaceTime =>
          u i (X p.1) * h i p.2)) p = u i (X p.1) * h i p.2 :=
      ae_all_iff.2 (fun i => (hterm i).coeFn_toLp)
    filter_upwards [hsum.coeFn_toLp, hsum', hterm_all] with p hp hs hall
    rw [hp]
    rw [hs]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hall i).symm
  rw [hDsum, hVsum]
  calc
    dist (∑ i, (hdi i).toLp (fun p : Ω × SpaceTime =>
        coordinateDerivative f i (X p.1) * h i p.2))
        (∑ i, (hterm i).toLp (fun p : Ω × SpaceTime => u i (X p.1) * h i p.2)) ≤
        ∑ i, dist ((hdi i).toLp (fun p : Ω × SpaceTime =>
          coordinateDerivative f i (X p.1) * h i p.2))
          ((hterm i).toLp (fun p : Ω × SpaceTime => u i (X p.1) * h i p.2)) := by
      rw [dist_eq_norm]
      rw [← Finset.sum_sub_distrib]
      simpa [dist_eq_norm] using
        (norm_sum_le (Finset.univ : Finset (Fin n))
          (fun i => (hdi i).toLp (fun p : Ω × SpaceTime =>
            coordinateDerivative f i (X p.1) * h i p.2) -
            (hterm i).toLp (fun p : Ω × SpaceTime => u i (X p.1) * h i p.2)))
    _ ≤ ∑ _i : Fin n, ε / ((2 : ℝ) * ((n : ℝ) + 1)) :=
      Finset.sum_le_sum (fun i hi => hdist_i i)
    _ < ε := by
      have hn : 0 < (n : ℝ) + 1 := by positivity
      calc
        ∑ _i : Fin n, ε / ((2 : ℝ) * ((n : ℝ) + 1)) =
            (n : ℝ) * (ε / ((2 : ℝ) * ((n : ℝ) + 1))) := by simp
        _ < ε := by
          have hhalf : ε / 2 < ε := by linarith
          calc
            (n : ℝ) * (ε / (2 * ((n : ℝ) + 1))) ≤
                ((n : ℝ) + 1) * (ε / (2 * ((n : ℝ) + 1))) := by
                  gcongr
                  linarith
            _ = ε / 2 := by field_simp
            _ < ε := hhalf

end RegularityStructures

end
