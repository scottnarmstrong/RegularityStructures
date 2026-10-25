/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincareSlices
public import RegularityStructures.Probability.GaussianLaw

set_option linter.style.haveILetI false

/-!
# The finite-dimensional Gaussian Poincare inequality

This is the genuine product-Gaussian tensorisation of the one-dimensional Stein inequality.  All
polynomial-growth and `L²` hypotheses are explicit.  The proof follows the product decomposition
of the standard Gaussian and the coordinate split at `0`; this is the finite-dimensional spectral
gap input in Hairer--Steele, Definition 2.20 and Remark 2.22.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

def coordinateEnergy {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, coordinateDerivative f i x ^ 2

private lemma norm_pi_single_one {n : ℕ} (i : Fin n) :
    ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
  rw [Pi.norm_single]
  norm_num

private lemma coordinateDerivative_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x => coordinateDerivative f i x) := by
  have h := hcont.continuous_fderiv_apply one_ne_zero
  simpa [coordinateDerivative, Function.comp_def] using h.comp
    (by fun_prop : Continuous (fun x : Fin n → ℝ => (x, Pi.single i 1)))

private lemma norm_real_continuousLinearMap_le_apply_one (L : ℝ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1| := by
  apply L.opNorm_le_bound (abs_nonneg _)
  intro x
  rw [show x = x • (1 : ℝ) by simp, map_smul]
  simp [Real.norm_eq_abs, mul_comm]

private lemma continuous_fin_cons_pair {n : ℕ} :
    Continuous (fun p : ℝ × (Fin n → ℝ) => finCons p.1 p.2) := by
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [finCons] using
      (continuous_fst : Continuous (fun p : ℝ × (Fin n → ℝ) => p.1))
  · have hfun : (fun p : ℝ × (Fin n → ℝ) => finCons p.1 p.2 i) =
        fun p => p.2 (i.pred hi) := by
      funext p
      calc
        finCons p.1 p.2 i = finCons p.1 p.2 ((i.pred hi).succ) :=
          congrArg (finCons p.1 p.2) (Fin.succ_pred i hi).symm
        _ = p.2 (i.pred hi) := by
          simpa [finCons] using
            (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) p.1 p.2 (i.pred hi))
    rw [hfun]
    exact (continuous_apply (i.pred hi)).comp continuous_snd

private lemma coordinateDerivative_bound_of_growth {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {C : ℝ} {N : ℕ} (_hC : 0 ≤ C)
    (hgrowth : ∀ x : Fin n → ℝ,
      |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (i : Fin n) :
    ∀ x : Fin n → ℝ,
      |coordinateDerivative f i x| ≤ C * (1 + ‖x‖) ^ N := by
  intro x
  have hnorm : ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (Pi.single i 1)
    simpa [norm_pi_single_one i] using h
  have hsum : ‖fderiv ℝ f x‖ ≤ |f x| + ‖fderiv ℝ f x‖ :=
    le_add_of_nonneg_left (abs_nonneg _)
  have h := hnorm.trans (hsum.trans (hgrowth x))
  simpa [coordinateDerivative, Real.norm_eq_abs] using h

private lemma integrable_coordinateEnergy_of_growth {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N) :
    Integrable (coordinateEnergy f) (standardGaussianMeasure n) := by
  haveI : IsGaussian (standardGaussianMeasure n) := isGaussian_standardGaussianMeasure n
  rcases hgrowth with ⟨C, N, hC, hgrowth⟩
  apply integrable_finsetSum
  intro i hi
  have hcoord : MemLp (fun x => coordinateDerivative f i x) 2
      (standardGaussianMeasure n) := by
    apply memLp_of_polynomial_bound_gaussian
    · exact (coordinateDerivative_continuous hcont i).measurable.aestronglyMeasurable
    · exact ⟨C, N, hC, coordinateDerivative_bound_of_growth hC hgrowth i⟩
  exact hcoord.integrable_sq

private lemma memLp_of_growth {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N) :
    MemLp f 2 (standardGaussianMeasure n) := by
  haveI : IsGaussian (standardGaussianMeasure n) := isGaussian_standardGaussianMeasure n
  rcases hgrowth with ⟨C, N, hC, hgrowth⟩
  refine memLp_of_polynomial_bound_gaussian hcont.continuous.measurable.aestronglyMeasurable ?_
  refine ⟨C, N, hC, ?_⟩
  intro x
  exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ f x))).trans (hgrowth x)

theorem gaussian_poincare_standard {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N) :
    Var[f; standardGaussianMeasure n] ≤
      ∫ x, coordinateEnergy f x ∂(standardGaussianMeasure n) := by
  induction n with
  | zero =>
      have hf : MemLp f 2 (standardGaussianMeasure 0) := memLp_of_growth hcont hgrowth
      have hconst : f = fun _ => f (fun i : Fin 0 => Fin.elim0 i) := by
        funext x
        congr
        funext i
        exact Fin.elim0 i
      rw [hconst]
      have hfconst : MemLp (fun _ : Fin 0 → ℝ => f (fun i : Fin 0 => Fin.elim0 i)) 2
          (standardGaussianMeasure 0) := by
        rw [← hconst]
        exact hf
      rw [variance_eq_integral hfconst.aemeasurable]
      have hprob : standardGaussianMeasure 0 Set.univ = 1 := by
        simp [standardGaussianMeasure]
      have hI : ∫ _ : Fin 0 → ℝ, f (fun i : Fin 0 => Fin.elim0 i)
          ∂(standardGaussianMeasure 0) = f (fun i : Fin 0 => Fin.elim0 i) := by
        rw [integral_const, measureReal_def, hprob]
        norm_num
      rw [hI]
      simp [coordinateEnergy]
  | succ n ih =>
      let μ : Fin (n + 1) → Measure ℝ := fun _ => gaussianReal 0 1
      let ν : Measure (Fin n → ℝ) := standardGaussianMeasure n
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let g : ℝ × (Fin n → ℝ) → ℝ := fun p => f (finCons p.1 p.2)
      let hprod : Measure (ℝ × (Fin n → ℝ)) := (gaussianReal 0 1).prod ν
      haveI : IsProbabilityMeasure ν := by
        dsimp [ν, standardGaussianMeasure]
        infer_instance
      haveI : IsProbabilityMeasure hprod := by
        dsimp [hprod]
        infer_instance
      have hμ : Measure.pi μ = standardGaussianMeasure (n + 1) := by
        rfl
      have hf : MemLp f 2 (standardGaussianMeasure (n + 1)) := memLp_of_growth hcont hgrowth
      have hfe : MemLp g 2 hprod := by
        have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
        have h := hf.comp_measurePreserving hmp
        have heq : f ∘ (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm = g := by
          funext p
          have hpoint : (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm p = finCons p.1 p.2 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            change Fin.insertNth 0 p.1 p.2 = finCons p.1 p.2
            rw [Fin.insertNth_zero']
            simp [finCons]
          simp only [Function.comp_apply, hpoint, g]
        rw [heq] at h
        simpa [hprod, μ, ν, standardGaussianMeasure] using h
      have hcont_scalar (y : Fin n → ℝ) :
          ContDiff ℝ 1 (fun x : ℝ => g (x, y)) := by
        simpa [g, Function.comp_def] using hcont.comp (contDiff_fin_cons_scalar y)
      have hcont_rest (x : ℝ) :
          ContDiff ℝ 1 (fun y : Fin n → ℝ => g (x, y)) := by
        simpa [g, Function.comp_def] using hcont.comp (contDiff_fin_cons_rest x)
      have hgrowth_value : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
          ∀ x : Fin (n + 1) → ℝ, |f x| ≤ C * (1 + ‖x‖) ^ N := by
        rcases hgrowth with ⟨C, N, hC, h⟩
        refine ⟨C, N, hC, ?_⟩
        intro x
        exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ f x))).trans (h x)
      obtain ⟨C, N, hC, hglobal⟩ := hgrowth
      have hvalue : ∀ x : Fin (n + 1) → ℝ,
          |f x| ≤ C * (1 + ‖x‖) ^ N := by
        intro x
        exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ f x))).trans (hglobal x)
      have hderiv : ∀ x : Fin (n + 1) → ℝ,
          ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N := by
        intro x
        exact (le_add_of_nonneg_left (abs_nonneg (f x))).trans (hglobal x)
      have hfx : ∀ x : ℝ, MemLp (fun y : Fin n → ℝ => g (x, y)) 2 ν := by
        intro x
        letI : IsGaussian ν := isGaussian_standardGaussianMeasure n
        rcases hgrowth_value with ⟨C, N, hC, hvalue⟩
        refine memLp_of_polynomial_bound_gaussian
          (hcont_rest x).continuous.measurable.aestronglyMeasurable ?_
        obtain ⟨D, hD, hbound⟩ := polynomial_bound_fin_cons_rest hC hvalue x
        refine ⟨D, N, hD, ?_⟩
        intro y
        simpa [g] using hbound y
      have hfy : ∀ y : Fin n → ℝ, MemLp (fun x : ℝ => g (x, y)) 2
          (gaussianReal 0 1) := by
        intro y
        refine memLp_polynomially_bounded_gaussian
          ((hcont_scalar y).continuous.measurable.aestronglyMeasurable) ?_ 2 (by norm_num)
        rcases hgrowth_value with ⟨C, N, hC, hvalue⟩
        obtain ⟨D, hD, hbound⟩ := polynomial_bound_fin_cons_scalar hC hvalue y
        refine ⟨D, N, hD, ?_⟩
        intro x
        simpa [g, Real.norm_eq_abs] using hbound x
      have hmean_fst : MemLp (fun x : ℝ => ∫ y, g (x, y) ∂ν) 2
          (gaussianReal 0 1) := memLp_integral_prod_left hfe hfx
      have hmean_snd : MemLp (fun y : Fin n → ℝ => ∫ x, g (x, y) ∂(gaussianReal 0 1)) 2 ν :=
        memLp_integral_prod_right hfe hfy
      have hvarprod := variance_prod_le_sum_slice_variances hfe hmean_fst hmean_snd hfx hfy
      have hvar_eq : Var[f; standardGaussianMeasure (n + 1)] = Var[g; hprod] := by
        have hmp := measurePreserving_piFinSuccAbove μ 0
        have hgmeas : AEMeasurable g hprod := hfe.aemeasurable
        have h := hmp.variance_fun_comp hgmeas
        have hgsym : f ∘ (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm = g := by
          funext p
          have hpoint : (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm p = finCons p.1 p.2 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            change Fin.insertNth 0 p.1 p.2 = finCons p.1 p.2
            rw [Fin.insertNth_zero']
            simp [finCons]
          simp only [Function.comp_apply, hpoint, g]
        have heq : (fun ω => g ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0) ω)) = f := by
          rw [show g = f ∘ (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm from hgsym.symm]
          funext ω
          exact congrArg f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => ℝ) 0).symm_apply_apply ω)
        rw [heq] at h
        simpa [hprod, μ, ν, standardGaussianMeasure] using h
      rw [hvar_eq]
      have hrest_growth (a : ℝ) : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧
          ∀ y : Fin n → ℝ,
            |g (a, y)| + ‖fderiv ℝ (fun z : Fin n → ℝ => g (a, z)) y‖ ≤
              D * (1 + ‖y‖) ^ M := by
        have hval := polynomial_bound_fin_cons_rest hC hvalue a
        have hnorm : ∀ x : Fin (n + 1) → ℝ,
            |‖fderiv ℝ f x‖| ≤ C * (1 + ‖x‖) ^ N := by
          intro x
          simpa [abs_of_nonneg (norm_nonneg _)] using hderiv x
        have hderiv' := polynomial_bound_fin_cons_rest hC hnorm a
        rcases hval with ⟨D, hD, hval⟩
        rcases hderiv' with ⟨D', hD', hderiv'⟩
        refine ⟨D + D', N, add_nonneg hD hD', ?_⟩
        intro y
        have hderiv_slice := fderiv_fin_cons_rest_norm_le hcont a y
        have hval' := hval y
        have hderiv_bound : ‖fderiv ℝ f (finCons a y)‖ ≤
            D' * (1 + ‖y‖) ^ N := by
          simpa [abs_of_nonneg (norm_nonneg _)] using hderiv' y
        have hderiv'' := hderiv_slice.trans hderiv_bound
        calc
          |g (a, y)| + ‖fderiv ℝ (fun z : Fin n → ℝ => g (a, z)) y‖ ≤
              D * (1 + ‖y‖) ^ N + D' * (1 + ‖y‖) ^ N := by
                simpa [g] using add_le_add hval' hderiv''
          _ = (D + D') * (1 + ‖y‖) ^ N := by ring
      have hrest_bound (a : ℝ) :
          Var[fun y : Fin n → ℝ => g (a, y); ν] ≤
            ∫ y, (∑ j : Fin n, coordinateDerivative f j.succ (finCons a y) ^ 2) ∂ν := by
        have h := ih (hcont_rest a) (hrest_growth a)
        calc
          Var[fun y : Fin n → ℝ => g (a, y); ν] ≤
              ∫ y, coordinateEnergy (fun z : Fin n → ℝ => g (a, z)) y ∂ν := h
          _ = ∫ y, (∑ j : Fin n, coordinateDerivative f j.succ (finCons a y) ^ 2) ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with y
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := coordinateDerivative_fin_cons_rest hcont a j y
            simp [g, hj']
      have hscalar_growth (y : Fin n → ℝ) :
          ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ a : ℝ,
            |g (a, y)| + ‖fderiv ℝ (fun t : ℝ => g (t, y)) a‖ ≤
              D * (1 + |a|) ^ M := by
        have hval := polynomial_bound_fin_cons_scalar hC hvalue y
        have hcoord := coordinateDerivative_bound_of_growth hC hglobal 0
        have hderiv0 := polynomial_bound_fin_cons_scalar hC hcoord y
        rcases hval with ⟨D, hD, hval⟩
        rcases hderiv0 with ⟨D', hD', hderiv0⟩
        refine ⟨D + D', N, add_nonneg hD hD', ?_⟩
        intro a
        have hderiv' := fderiv_fin_cons_scalar hcont a y
        have hval' := hval a
        have hderiv'' : ‖fderiv ℝ (fun t : ℝ => g (t, y)) a‖ ≤
            D' * (1 + |a|) ^ N := by
          change ‖fderiv ℝ (fun t : ℝ => f (finCons t y)) a‖ ≤
            D' * (1 + |a|) ^ N
          have hnorm := norm_real_continuousLinearMap_le_apply_one
            (fderiv ℝ (fun t : ℝ => f (finCons t y)) a)
          rw [fderiv_fin_cons_scalar hcont a y] at hnorm
          exact hnorm.trans (by simpa [coordinateDerivative] using hderiv0 a)
        calc
          |g (a, y)| + ‖fderiv ℝ (fun t : ℝ => g (t, y)) a‖ ≤
              D * (1 + |a|) ^ N + D' * (1 + |a|) ^ N := by
                simpa [g] using add_le_add hval' hderiv''
          _ = (D + D') * (1 + |a|) ^ N := by ring
      have hscalar_bound (y : Fin n → ℝ) :
          Var[fun a : ℝ => g (a, y); gaussianReal 0 1] ≤
            ∫ a, coordinateDerivative f 0 (finCons a y) ^ 2 ∂(gaussianReal 0 1) := by
        have h := gaussian_poincare_one_dimensional_of_polynomial_growth
          (hcont_scalar y) (hscalar_growth y)
        calc
          Var[fun a : ℝ => g (a, y); gaussianReal 0 1] ≤
              ∫ a, (fderiv ℝ (fun t : ℝ => g (t, y)) a 1) ^ 2
                ∂(gaussianReal 0 1) := h
          _ = ∫ a, coordinateDerivative f 0 (finCons a y) ^ 2
                ∂(gaussianReal 0 1) := by
            apply integral_congr_ae
            filter_upwards [] with a
            rw [fderiv_fin_cons_scalar hcont a y]
            rfl
      have hrest_var_int : Integrable
          (fun a : ℝ => Var[fun y : Fin n → ℝ => g (a, y); ν])
          (gaussianReal 0 1) := by
        have hsq : Integrable (fun a : ℝ => ∫ y, g (a, y) ^ 2 ∂ν)
            (gaussianReal 0 1) := hfe.integrable_sq.integral_prod_left
        have hmean_sq := hmean_fst.integrable_sq
        have hvar : (fun a : ℝ => Var[fun y : Fin n → ℝ => g (a, y); ν]) =
            (fun a : ℝ => (∫ y, g (a, y) ^ 2 ∂ν) - (∫ y, g (a, y) ∂ν) ^ 2) := by
              funext a
              rw [variance_eq_sub (hfx a)]
              simp only [Pi.pow_apply]
        rw [hvar]
        exact hsq.sub hmean_sq
      have hscalar_var_int : Integrable
          (fun y : Fin n → ℝ => Var[fun a : ℝ => g (a, y); gaussianReal 0 1]) ν := by
        have hsq : Integrable (fun y : Fin n → ℝ => ∫ a, g (a, y) ^ 2
            ∂(gaussianReal 0 1)) ν := hfe.integrable_sq.integral_prod_right
        have hmean_sq := hmean_snd.integrable_sq
        have hvar : (fun y : Fin n → ℝ => Var[fun a : ℝ => g (a, y); gaussianReal 0 1]) =
            (fun y : Fin n → ℝ => (∫ a, g (a, y) ^ 2 ∂(gaussianReal 0 1)) -
              (∫ a, g (a, y) ∂(gaussianReal 0 1)) ^ 2) := by
              funext y
              rw [variance_eq_sub (hfy y)]
              simp only [Pi.pow_apply]
        rw [hvar]
        exact hsq.sub hmean_sq
      have hrest_int : Integrable (fun p : ℝ × (Fin n → ℝ) =>
          ∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2) hprod := by
        have htotal := integrable_coordinateEnergy_of_growth hcont ⟨C, N, hC, hglobal⟩
        have hpi : Integrable (coordinateEnergy f) (Measure.pi μ) := by
          rw [hμ]
          exact htotal
        have hcomp := (measurePreserving_piFinSuccAbove μ 0).symm.integrable_comp_of_integrable hpi
        have hfun : (coordinateEnergy f) ∘
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm =
            fun p : ℝ × (Fin n → ℝ) => coordinateEnergy f (finCons p.1 p.2) := by
          funext p
          rw [Function.comp_apply]
          have hp : (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm p = finCons p.1 p.2 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            change Fin.insertNth 0 p.1 p.2 = finCons p.1 p.2
            rw [Fin.insertNth_zero']
            simp [finCons]
          rw [hp]
        rw [hfun] at hcomp
        have hnonneg : ∀ p : ℝ × (Fin n → ℝ), 0 ≤
            ∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2 := by
          intro p
          exact Finset.sum_nonneg fun j hj => sq_nonneg _
        have hle : ∀ p : ℝ × (Fin n → ℝ),
            (∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2) ≤
            coordinateEnergy f (finCons p.1 p.2) := by
          intro p
          simp only [coordinateEnergy, Fin.sum_univ_succ]
          nlinarith [sq_nonneg (coordinateDerivative f 0 (finCons p.1 p.2))]
        refine hcomp.mono' ?_ ?_
        · have hcontsum : Continuous (fun p : ℝ × (Fin n → ℝ) =>
              ∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2) := by
            simpa using
              (continuous_finsetSum (f := fun (j : Fin n) (p : ℝ × (Fin n → ℝ)) =>
                coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2) Finset.univ (by
                  intro j hj
                  exact ((coordinateDerivative_continuous hcont j.succ).comp
                    continuous_fin_cons_pair).pow 2))
          exact hcontsum.aestronglyMeasurable
        · filter_upwards [] with p
          simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg p)] using hle p
      have hfirst_int : Integrable (fun p : ℝ × (Fin n → ℝ) =>
          coordinateDerivative f 0 (finCons p.1 p.2) ^ 2) hprod := by
        have htotal := integrable_coordinateEnergy_of_growth hcont ⟨C, N, hC, hglobal⟩
        have hpi : Integrable (coordinateEnergy f) (Measure.pi μ) := by
          rw [hμ]
          exact htotal
        have hcomp := (measurePreserving_piFinSuccAbove μ 0).symm.integrable_comp_of_integrable hpi
        have hfun : (coordinateEnergy f) ∘
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm =
            fun p : ℝ × (Fin n → ℝ) => coordinateEnergy f (finCons p.1 p.2) := by
          funext p
          rw [Function.comp_apply]
          have hp : (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0).symm p = finCons p.1 p.2 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            change Fin.insertNth 0 p.1 p.2 = finCons p.1 p.2
            rw [Fin.insertNth_zero']
            simp [finCons]
          rw [hp]
        rw [hfun] at hcomp
        have hle : ∀ p : ℝ × (Fin n → ℝ), coordinateDerivative f 0 (finCons p.1 p.2) ^ 2 ≤
            coordinateEnergy f (finCons p.1 p.2) := by
          intro p
          simp only [coordinateEnergy, Fin.sum_univ_succ]
          have hnonneg : 0 ≤ ∑ j : Fin n, coordinateDerivative f j.succ
              (finCons p.1 p.2) ^ 2 :=
            Finset.sum_nonneg fun j hj => sq_nonneg _
          nlinarith
        refine hcomp.mono' ?_ ?_
        · exact ((coordinateDerivative_continuous hcont 0).comp continuous_fin_cons_pair).pow 2 |>.aestronglyMeasurable
        · filter_upwards [] with p
          have hs : 0 ≤ coordinateDerivative f 0 (finCons p.1 p.2) ^ 2 := sq_nonneg _
          simpa [Real.norm_eq_abs, abs_of_nonneg hs] using hle p
      have hrest_energy_int : Integrable (fun a : ℝ =>
          ∫ y, (∑ j : Fin n, coordinateDerivative f j.succ (finCons a y) ^ 2) ∂ν)
          (gaussianReal 0 1) := hrest_int.integral_prod_left
      have hfirst_energy_int : Integrable (fun y : Fin n → ℝ =>
          ∫ a, coordinateDerivative f 0 (finCons a y) ^ 2
            ∂(gaussianReal 0 1)) ν := hfirst_int.integral_prod_right
      have hrest_mono :
          ∫ a, Var[fun y : Fin n → ℝ => g (a, y); ν] ∂(gaussianReal 0 1) ≤
            ∫ a, (∫ y, (∑ j : Fin n, coordinateDerivative f j.succ (finCons a y) ^ 2) ∂ν)
              ∂(gaussianReal 0 1) :=
        integral_mono hrest_var_int hrest_energy_int hrest_bound
      have hscalar_mono :
          ∫ y, Var[fun a : ℝ => g (a, y); gaussianReal 0 1] ∂ν ≤
            ∫ y, (∫ a, coordinateDerivative f 0 (finCons a y) ^ 2
              ∂(gaussianReal 0 1)) ∂ν :=
        integral_mono hscalar_var_int hfirst_energy_int hscalar_bound
      calc
        Var[g; hprod] ≤
            ∫ a, Var[fun y : Fin n → ℝ => g (a, y); ν] ∂(gaussianReal 0 1) +
              ∫ y, Var[fun a : ℝ => g (a, y); gaussianReal 0 1] ∂ν := hvarprod
        _ ≤
            ∫ a, (∫ y, (∑ j : Fin n, coordinateDerivative f j.succ (finCons a y) ^ 2) ∂ν)
              ∂(gaussianReal 0 1) +
              ∫ y, (∫ a, coordinateDerivative f 0 (finCons a y) ^ 2
                ∂(gaussianReal 0 1)) ∂ν := add_le_add hrest_mono hscalar_mono
        _ = ∫ p, coordinateEnergy f (finCons p.1 p.2) ∂hprod := by
          rw [← integral_prod _ hrest_int, ← integral_prod_symm _ hfirst_int]
          have hsum : ∀ p : ℝ × (Fin n → ℝ),
              coordinateEnergy f (finCons p.1 p.2) =
                coordinateDerivative f 0 (finCons p.1 p.2) ^ 2 +
                  ∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2 := by
            intro p
            simp [coordinateEnergy, Fin.sum_univ_succ]
          rw [← integral_add hrest_int hfirst_int]
          apply integral_congr_ae
          filter_upwards [] with p
          calc
            (∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2) +
                coordinateDerivative f 0 (finCons p.1 p.2) ^ 2 =
                coordinateDerivative f 0 (finCons p.1 p.2) ^ 2 +
                  ∑ j : Fin n, coordinateDerivative f j.succ (finCons p.1 p.2) ^ 2 := by
                    ring
            _ = coordinateEnergy f (finCons p.1 p.2) := (hsum p).symm
        _ = ∫ x, coordinateEnergy f x ∂(standardGaussianMeasure (n + 1)) := by
          have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
          have h := hmp.integral_comp' (coordinateEnergy f)
          have hfun : (fun x : ℝ × (Fin n → ℝ) =>
              coordinateEnergy f ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (n + 1) => ℝ) 0).symm x)) =
              (fun x : ℝ × (Fin n → ℝ) => coordinateEnergy f (finCons x.1 x.2)) := by
            funext x
            congr 1
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            change Fin.insertNth 0 x.1 x.2 = finCons x.1 x.2
            rw [Fin.insertNth_zero']
            simp [finCons]
          rw [← hfun]
          simpa [μ, ν, hprod, standardGaussianMeasure] using h

end RegularityStructures

end
