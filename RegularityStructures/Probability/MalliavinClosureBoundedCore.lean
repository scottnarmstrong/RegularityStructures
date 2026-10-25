/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounded chain and product rules on the cylindrical core

This module supplies the explicit `L²` bookkeeping needed by the cylindrical chain and product
identities.  A bounded derivative gives the scalar composition its required `L²` value and
derivative bounds; bounded cylindrical factors give the corresponding product bounds.  The
polynomial-growth assumptions on the resulting finite-dimensional functions remain explicit.
These are the core rules used when applying the closure transport theorems to `D^{1,2}`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RegularityStructures

private lemma malliavin_lipschitz_sub_const
    {φ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) :
    LipschitzWith C (fun x => φ x - φ 0) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simpa [dist_eq_norm, sub_sub] using hφ.dist_le_mul x y

private lemma malliavin_deriv_norm_le
    {φ : ℝ → ℝ} {C : ℝ≥0}
    (hC : ∀ x, ‖deriv φ x‖₊ ≤ C) (x : ℝ) :
    ‖deriv φ x‖ ≤ (C : ℝ) := by
  exact_mod_cast hC x

private lemma malliavin_chain_value_memLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {φ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) {F : Ω → ℝ} (hF : MemLp F 2 P) :
    MemLp (fun ω => φ (F ω)) 2 P := by
  let ψ : ℝ → ℝ := fun x => φ x - φ 0
  have hψ : LipschitzWith C ψ := malliavin_lipschitz_sub_const hφ
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hcomp : MemLp (ψ ∘ F) 2 P := hψ.comp_memLp hψ0 hF
  have hone : MemLp (fun _ : Ω => φ 0) 2 P :=
    MeasureTheory.memLp_const (p := (2 : ℝ≥0∞)) (μ := P) (φ 0)
  have hsum := hcomp.add hone
  convert hsum using 1
  funext ω
  simp [ψ, Function.comp_def]

theorem malliavin_cylindrical_chain_rule_bounded_derivative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    {φ : ℝ → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem : ∀ i, MemLp (h i) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_φ : ContDiff ℝ 1 φ)
    (hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_φf : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |φ (f x)| +
        ‖fderiv ℝ (fun y => φ (f y)) x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hφ_bound : ∃ C : ℝ≥0, ∀ x, ‖deriv φ x‖₊ ≤ C)
    (hF : MemLp (cylindricalFunctional W h f) 2 P)
    (hD : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P)) :
    ∃ hφF : MemLp (fun ω => φ (cylindricalFunctional W h f ω)) 2 P,
      ∃ hφD : MemLp (fun p : Ω × SpaceTime =>
        ∑ i, coordinateDerivative (fun y => φ (f y)) i
          (fun j => W (h j) p.1) * h i p.2) 2
          (whiteNoiseDerivativeMeasure P),
        (hφF.toLp (fun ω => φ (cylindricalFunctional W h f ω)),
          hφD.toLp (fun p : Ω × SpaceTime =>
            ∑ i, coordinateDerivative (fun y => φ (f y)) i
              (fun j => W (h j) p.1) * h i p.2)) ∈
          cylindricalMalliavinGraph P W := by
  obtain ⟨C, hC⟩ := hφ_bound
  have hφ_lip : LipschitzWith C φ :=
    lipschitzWith_of_nnnorm_deriv_le (hcont_φ.differentiable one_ne_zero) hC
  have hφF : MemLp (fun ω => φ (cylindricalFunctional W h f ω)) 2 P := by
    exact malliavin_chain_value_memLp hφ_lip hF
  let X : Ω → Fin n → ℝ := fun ω i => W (h i) ω
  let Df : Ω × SpaceTime → ℝ := fun p =>
    cylindricalDerivative W h f p.1 p.2
  let Dφ : Ω × SpaceTime → ℝ := fun p =>
    ∑ i, coordinateDerivative (fun y => φ (f y)) i
      (fun j => W (h j) p.1) * h i p.2
  have hXmeas : Measurable X := by
    rw [measurable_pi_iff]
    intro i
    exact hW.1 (h i) (hmem i)
  have hmult_meas : AEStronglyMeasurable
      (fun p : Ω × SpaceTime => deriv φ (f (X p.1)))
      (whiteNoiseDerivativeMeasure P) := by
    have hm : Measurable (fun p : Ω × SpaceTime => deriv φ (f (X p.1))) :=
      (hcont_φ.continuous_deriv_one.measurable.comp
        (hcont_f.continuous.measurable.comp (hXmeas.comp measurable_fst)))
    exact hm.aestronglyMeasurable
  have hDφ_meas : AEStronglyMeasurable Dφ
      (whiteNoiseDerivativeMeasure P) := by
    have heq : Dφ = fun p => deriv φ (f (X p.1)) * Df p := by
      funext p
      dsimp [Dφ, Df, X, cylindricalDerivative]
      simp_rw [coordinateDerivative_comp_scalar hcont_f hcont_φ]
      calc
        _ = ∑ i, deriv φ (f (fun j => W (h j) p.1)) *
            (coordinateDerivative f i (fun j => W (h j) p.1) * h i p.2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.mul_sum]
    rw [heq]
    exact hmult_meas.mul hD.aestronglyMeasurable
  have hDφ : MemLp Dφ 2 (whiteNoiseDerivativeMeasure P) := by
    apply hD.of_le_mul hDφ_meas
    filter_upwards [] with p
    have hpoint : ‖deriv φ (f (X p.1))‖ ≤ (C : ℝ) :=
      malliavin_deriv_norm_le hC _
    calc
      ‖Dφ p‖ = ‖deriv φ (f (X p.1)) * Df p‖ := by
        congr 1
        rw [show Dφ p = deriv φ (f (X p.1)) * Df p by
          dsimp [Dφ, Df, X, cylindricalDerivative]
          simp_rw [coordinateDerivative_comp_scalar hcont_f hcont_φ]
          calc
            _ = ∑ i, deriv φ (f (fun j => W (h j) p.1)) *
                (coordinateDerivative f i (fun j => W (h j) p.1) * h i p.2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = _ := by rw [Finset.mul_sum]]
      _ = ‖deriv φ (f (X p.1))‖ * ‖Df p‖ := norm_mul _ _
      _ ≤ (C : ℝ) * ‖Df p‖ :=
        mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
  refine ⟨hφF, hDφ, ?_⟩
  simpa [Dφ] using
    (cylindricalMalliavinGraph_chain_rule hmem hcont_f hcont_φ hgrowth_f
      hgrowth_φf hF hD hφF hDφ)

theorem malliavin_cylindrical_product_rule_bounded_values
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ}
    {f g : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem : ∀ i, MemLp (h i) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_prod : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x * g x| +
        ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hf_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B)
    (hg_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B)
    (hF : MemLp (cylindricalFunctional W h f) 2 P)
    (hD : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P))
    (hG : MemLp (cylindricalFunctional W h g) 2 P)
    (hDG : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h g p.1 p.2) 2 (whiteNoiseDerivativeMeasure P)) :
    ∃ hFG : MemLp (fun ω => cylindricalFunctional W h f ω *
        cylindricalFunctional W h g ω) 2 P,
      ∃ hDprod : MemLp (fun p : Ω × SpaceTime =>
        ∑ i, coordinateDerivative (fun y => f y * g y) i
          (fun j => W (h j) p.1) * h i p.2) 2
          (whiteNoiseDerivativeMeasure P),
        (hFG.toLp (fun ω => cylindricalFunctional W h f ω *
            cylindricalFunctional W h g ω),
          hDprod.toLp (fun p : Ω × SpaceTime =>
            ∑ i, coordinateDerivative (fun y => f y * g y) i
              (fun j => W (h j) p.1) * h i p.2)) ∈
          cylindricalMalliavinGraph P W := by
  obtain ⟨Bf, hBf, hfb⟩ := hf_bound
  obtain ⟨Bg, hBg, hgb⟩ := hg_bound
  let F : Ω → ℝ := cylindricalFunctional W h f
  let G : Ω → ℝ := cylindricalFunctional W h g
  let X : Ω → Fin n → ℝ := fun ω i => W (h i) ω
  let Df : Ω × SpaceTime → ℝ := fun p => cylindricalDerivative W h f p.1 p.2
  let Dg : Ω × SpaceTime → ℝ := fun p => cylindricalDerivative W h g p.1 p.2
  let Dprod : Ω × SpaceTime → ℝ := fun p =>
    ∑ i, coordinateDerivative (fun y => f y * g y) i
      (fun j => W (h j) p.1) * h i p.2
  have hFG_meas : AEStronglyMeasurable (fun ω => F ω * G ω) P :=
    hF.aestronglyMeasurable.mul hG.aestronglyMeasurable
  have hFmeas : Measurable F := by
    exact cylindricalFunctional_measurable hW hmem hcont_f
  have hGmeas : Measurable G := by
    exact cylindricalFunctional_measurable hW hmem hcont_g
  have hFG : MemLp (fun ω => F ω * G ω) 2 P := by
    apply hG.of_le_mul hFG_meas
    filter_upwards [] with ω
    calc
      ‖F ω * G ω‖ = |F ω| * ‖G ω‖ := by rw [norm_mul, Real.norm_eq_abs]
      _ ≤ Bf * ‖G ω‖ := mul_le_mul_of_nonneg_right (hfb _) (norm_nonneg _)
  have hDprod_eq : Dprod = fun p => Df p * G p.1 + F p.1 * Dg p := by
    funext p
    dsimp [Dprod, Df, Dg, F, G, cylindricalDerivative]
    simp_rw [coordinateDerivative_mul hcont_f hcont_g]
    calc
      _ = ∑ i, (coordinateDerivative f i (fun j => W (h j) p.1) *
          (g (fun j => W (h j) p.1) * h i p.2) +
          f (fun j => W (h j) p.1) *
            (coordinateDerivative g i (fun j => W (h j) p.1) * h i p.2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, coordinateDerivative f i (fun j => W (h j) p.1) * h i p.2) *
          g (fun j => W (h j) p.1) +
          f (fun j => W (h j) p.1) *
            ∑ i, coordinateDerivative g i (fun j => W (h j) p.1) * h i p.2 := by
        rw [Finset.sum_add_distrib]
        calc
          _ = (∑ i, (coordinateDerivative f i (fun j => W (h j) p.1) *
              h i p.2) * g (fun j => W (h j) p.1)) +
              ∑ i, f (fun j => W (h j) p.1) *
                (coordinateDerivative g i (fun j => W (h j) p.1) * h i p.2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.sum_mul, Finset.mul_sum]
  have hterm_f : MemLp (fun p => Df p * G p.1) 2
      (whiteNoiseDerivativeMeasure P) := by
    apply hD.of_le_mul (hD.aestronglyMeasurable.mul
      (hGmeas.comp measurable_fst).aestronglyMeasurable)
    filter_upwards [] with p
    have hGp : ‖G p.1‖ ≤ Bg := by
      simpa [G, cylindricalFunctional] using hgb (X p.1)
    calc
      ‖Df p * G p.1‖ = ‖Df p‖ * ‖G p.1‖ := norm_mul _ _
      _ ≤ ‖Df p‖ * Bg := mul_le_mul_of_nonneg_left hGp (norm_nonneg _)
      _ = Bg * ‖Df p‖ := by ring
  have hterm_g : MemLp (fun p => F p.1 * Dg p) 2
      (whiteNoiseDerivativeMeasure P) := by
    apply hDG.of_le_mul ((hFmeas.comp measurable_fst).aestronglyMeasurable.mul
      hDG.aestronglyMeasurable)
    filter_upwards [] with p
    have hFp : ‖F p.1‖ ≤ Bf := by
      simpa [F, cylindricalFunctional] using hfb (X p.1)
    calc
      ‖F p.1 * Dg p‖ = ‖F p.1‖ * ‖Dg p‖ := norm_mul _ _
      _ ≤ Bf * ‖Dg p‖ := mul_le_mul_of_nonneg_right hFp (norm_nonneg _)
  have hDprod : MemLp Dprod 2 (whiteNoiseDerivativeMeasure P) := by
    rw [hDprod_eq]
    exact hterm_f.add hterm_g
  refine ⟨hFG, hDprod, ?_⟩
  simpa [F, G, Df, Dg, Dprod] using
    (cylindricalMalliavinGraph_product_rule hmem hcont_f hcont_g hgrowth_f
      hgrowth_prod hF hD hFG hDprod)

end RegularityStructures

end
