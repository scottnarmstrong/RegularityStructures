/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.FundamentalSolution
public import Phi43.Potential.QKernel
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import RegularityStructures.Abstract.Integration.PolyPairing.Vanish

/-!
# Integration by parts for the smooth remainder `R = annRemainderC N`

For a smooth space-periodic `ψ` vanishing for `|t| > b`,
`∫ R · L^*ψ = ∫ Q · ψ` with `Q = (∂_t - Δ) R = potQ N` (`integral_annRemainder_lstar`): the
derivatives of `R` decay rapidly in space (`RemKernel.decay`) and `ψ` and its derivatives are
bounded with support in `|t| ≤ b`, so all products are integrable and
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` applies.
-/

public section

open Set MeasureTheory Filter RegularityStructures.Inhomogeneity RegularityStructures.Potential
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem coordDir_eq_stBasis (j : Fin 4) : coordDir j = Datum.stBasis j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · ext <;> simp [coordDir_succ, spaceDir, Datum.stBasis, Datum.stOfCoords, Pi.single_apply]

theorem lineIter_map_coordDir (r : ParabolicSpace → ℝ) :
    ∀ L : List (Fin 4), lineIter (L.map coordDir) r = ddA L r
  | [] => rfl
  | j :: L => by
      funext z
      simp only [List.map_cons, lineIter]
      rw [lineIter_map_coordDir r L]
      simp only [dirDeriv, ddA, ddv, coordDir_eq_stBasis]

theorem inv_one_add_sqNorm3_sq_le (v : Fin 3 → ℝ) :
    ((1 + sqNorm3 v)⁻¹) ^ 2 ≤ 4 * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  have hs : ‖v‖ ^ 2 ≤ sqNorm3 v := by
    have hi : ∀ i, |v i| ^ 2 ≤ sqNorm3 v := fun i => by
      unfold sqNorm3
      rw [sq_abs]
      exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hnn : 0 ≤ sqNorm3 v := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : ‖v‖ ≤ Real.sqrt (sqNorm3 v) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact Real.le_sqrt_of_sq_le (hi i)
    calc ‖v‖ ^ 2 ≤ (Real.sqrt (sqNorm3 v)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = sqNorm3 v := Real.sq_sqrt hnn
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  have hpos : 0 < 1 + sqNorm3 v := by
    have : 0 ≤ sqNorm3 v := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have h1 : (1 + ‖v‖) ^ 2 ≤ 2 * (1 + sqNorm3 v) := by nlinarith [sq_nonneg (‖v‖ - 1), hs]
  have h2 : (1 + sqNorm3 v)⁻¹ ≤ 2 * ((1 + ‖v‖) ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one, div_le_div_iff₀ hpos (by positivity)]
    linarith
  have h3 : ((1 + sqNorm3 v)⁻¹) ^ 2 ≤ (2 * ((1 + ‖v‖) ^ 2)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc ((1 + sqNorm3 v)⁻¹) ^ 2 ≤ (2 * ((1 + ‖v‖) ^ 2)⁻¹) ^ 2 := h3
    _ = 4 * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
        ring

theorem exists_abs_ddA_annRemainderC_le (N : ℕ) (L : List (Fin 4)) (T₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ →
      |ddA L (annRemainderC N) z| ≤ C * (1 + ‖z.2‖) ^ (-(4 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := (remKernel_annRemainderC N).decay L 2 T₀
  refine ⟨4 * C, by positivity, fun z hz => ?_⟩
  have := hC z hz
  rw [lineIter_map_coordDir] at this
  calc |ddA L (annRemainderC N) z| ≤ C * ((1 + sqNorm3 z.2)⁻¹) ^ 2 := this
    _ ≤ C * (4 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (inv_one_add_sqNorm3_sq_le _) hC0
    _ = 4 * C * (1 + ‖z.2‖) ^ (-(4 : ℝ)) := by ring

/-- A smooth periodic function vanishing for `|t| > b` is bounded. -/
theorem exists_bound_of_support {φ : ParabolicSpace → ℝ} (hφ : PerSmooth φ) {b : ℝ}
    (hs : ∀ w : ParabolicSpace, b < |w.1| → φ w = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w, |φ w| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -b) (b := b)).exists_bound_of_continuousOn
    (continuous_forcePath hφ).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : b < |w.1|
  · rw [hs w hw, abs_zero]; exact le_max_right _ _
  · have hw' : w.1 ∈ Icc (-b) b := abs_le.1 (not_lt.1 hw)
    have h2 : |φ w| ≤ ‖forcePath hφ w.1‖ := by
      have := (forcePath hφ w.1).norm_coe_le_norm (torusProj w.2)
      rwa [forcePath_apply, Real.norm_eq_abs] at this
    exact h2.trans ((hM w.1 hw').trans (le_max_left _ _))

theorem ddv_eq_zero_of_support {F : ParabolicSpace → ℝ} {b : ℝ}
    (hF : ∀ w : ParabolicSpace, b < |w.1| → F w = 0) (j : Fin 4) :
    ∀ w : ParabolicSpace, b < |w.1| → ddv j F w = 0 := by
  have hopen : IsOpen {w : ParabolicSpace | b < |w.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  intro w hw
  have : F =ᶠ[nhds w] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hw) fun w' hw' => hF w' hw'
  simp only [ddv, this.fderiv_eq]
  simp

/-- A kernel with rapid spatial decay times a bounded function supported in `|t| ≤ b`. -/
theorem integrable_decay_mul {k φ : ParabolicSpace → ℝ} (hk : Continuous k) (hφ : Continuous φ)
    {b C M : ℝ} (hC : 0 ≤ C) (hkb : ∀ w : ParabolicSpace, w.1 ≤ b → |k w| ≤ C * (1 + ‖w.2‖) ^ (-(4 : ℝ)))
    (hφb : ∀ w, |φ w| ≤ M) (hφs : ∀ w : ParabolicSpace, b < |w.1| → φ w = 0) :
    Integrable (fun w => k w * φ w) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφb 0)
  have h1 : Integrable ((Icc (-b) b).indicator fun _ : ℝ => C * M) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) enorm_ne_top)
  have h2 : Integrable (fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hD : Integrable (fun w : ParabolicSpace =>
      (Icc (-b) b).indicator (fun _ : ℝ => C * M) w.1 * (1 + ‖w.2‖) ^ (-(4 : ℝ))) := by
    rw [Measure.volume_eq_prod]
    exact h1.mul_prod h2
  refine hD.mono' (hk.mul hφ).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hw : b < |w.1|
  · rw [hφs w hw, abs_zero, mul_zero]
    refine mul_nonneg (indicator_nonneg (fun _ _ => by positivity) _) (Real.rpow_nonneg (by positivity) _)
  · have hw' : w.1 ∈ Icc (-b) b := abs_le.1 (not_lt.1 hw)
    rw [indicator_of_mem hw']
    calc |k w| * |φ w| ≤ (C * (1 + ‖w.2‖) ^ (-(4 : ℝ))) * M :=
          mul_le_mul (hkb w hw'.2) (hφb w) (abs_nonneg _) (by positivity)
      _ = C * M * (1 + ‖w.2‖) ^ (-(4 : ℝ)) := by ring

theorem integral_mul_ddv {f φ : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (j : Fin 4) (h1 : Integrable (fun w => ddv j f w * φ w))
    (h2 : Integrable (fun w => f w * ddv j φ w)) (h3 : Integrable (fun w => f w * φ w)) :
    ∫ w, f w * ddv j φ w = -∫ w, ddv j f w * φ w := by
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hdf : ∀ x, DifferentiableAt ℝ f x := fun x => (hf.differentiable (by simp)) x
  have hdφ : ∀ x, DifferentiableAt ℝ φ x := fun x => (hφ.differentiable (by simp)) x
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := Datum.stBasis j) h1 h2 h3
    (fun x _ => hdf x) (fun x _ => hdφ x)

theorem integrable_ddA_mul (N : ℕ) (L : List (Fin 4)) {φ : ParabolicSpace → ℝ} (hφ : PerSmooth φ)
    {b : ℝ} (hs : ∀ w : ParabolicSpace, b < |w.1| → φ w = 0) :
    Integrable (fun w => ddA L (annRemainderC N) w * φ w) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_ddA_annRemainderC_le N L b
  obtain ⟨M, -, hM⟩ := exists_bound_of_support hφ hs
  exact integrable_decay_mul (contDiff_ddA (contDiff_annRemainderC N) L).continuous
    hφ.smooth.continuous hC0 hC hM hs

/-- **Integration by parts for the remainder**: `∫ R · L^*ψ = ∫ Q · ψ`. -/
theorem integral_annRemainder_lstar (N : ℕ) {ψ : ParabolicSpace → ℝ} (hψ : PerSmooth ψ) {b : ℝ}
    (hs : ∀ w : ParabolicSpace, b < |w.1| → ψ w = 0) :
    ∫ w, annRemainderC N w * lstar ψ w = ∫ w, potQ N w * ψ w := by
  set R := annRemainderC N with hR
  have hRs : ContDiff ℝ ∞ R := contDiff_annRemainderC N
  have hdd : ∀ (L : List (Fin 4)), ContDiff ℝ ∞ (ddA L R) := fun L => contDiff_ddA hRs L
  -- smoothness, periodicity and supports of the derivatives of `ψ`
  have hψ1 : ∀ j : Fin 4, PerSmooth (ddv j ψ) := fun j => hψ.ddv j
  have hs1 : ∀ j : Fin 4, ∀ w : ParabolicSpace, b < |w.1| → ddv j ψ w = 0 :=
    fun j => ddv_eq_zero_of_support hs j
  have hψ2 : ∀ j : Fin 4, PerSmooth (ddv j (ddv j ψ)) := fun j => (hψ1 j).ddv j
  have hs2 : ∀ j : Fin 4, ∀ w : ParabolicSpace, b < |w.1| → ddv j (ddv j ψ) w = 0 :=
    fun j => ddv_eq_zero_of_support (hs1 j) j
  -- the integrals
  have iR0 := integrable_ddA_mul N [] hψ hs
  have iR1 : ∀ j : Fin 4, Integrable (fun w => R w * ddv j ψ w) := fun j =>
    integrable_ddA_mul N [] (hψ1 j) (hs1 j)
  have iR2 : ∀ j : Fin 4, Integrable (fun w => R w * ddv j (ddv j ψ) w) := fun j =>
    integrable_ddA_mul N [] (hψ2 j) (hs2 j)
  have iD1 : ∀ j : Fin 4, Integrable (fun w => ddv j R w * ψ w) := fun j =>
    integrable_ddA_mul N [j] hψ hs
  have iD1' : ∀ j : Fin 4, Integrable (fun w => ddv j R w * ddv j ψ w) := fun j =>
    integrable_ddA_mul N [j] (hψ1 j) (hs1 j)
  have iD2 : ∀ j : Fin 4, Integrable (fun w => ddv j (ddv j R) w * ψ w) := fun j =>
    integrable_ddA_mul N [j, j] hψ hs
  -- integration by parts
  have e0 : ∫ w, R w * ddv 0 ψ w = -∫ w, ddv 0 R w * ψ w :=
    integral_mul_ddv hRs hψ.smooth 0 (iD1 0) (iR1 0) iR0
  have ej : ∀ j : Fin 3, ∫ w, R w * ddv j.succ (ddv j.succ ψ) w =
      ∫ w, ddv j.succ (ddv j.succ R) w * ψ w := by
    intro j
    have a1 := integral_mul_ddv hRs (hψ1 j.succ).smooth j.succ (iD1' j.succ) (iR2 j.succ) (iR1 j.succ)
    have a2 := integral_mul_ddv (hdd [j.succ]) hψ.smooth j.succ (iD2 j.succ) (iD1' j.succ) (iD1 j.succ)
    rw [a1]
    have : ∫ w, ddv j.succ R w * ddv j.succ ψ w = -∫ w, ddv j.succ (ddv j.succ R) w * ψ w := a2
    rw [this, neg_neg]
  -- assembly
  have hL : (fun w => R w * lstar ψ w) = fun w => -(R w * ddv 0 ψ w) -
      ∑ j : Fin 3, R w * ddv j.succ (ddv j.succ ψ) w := by
    funext w
    simp only [lstar, mul_sub, mul_neg, Finset.mul_sum]
  have hQ : (fun w => potQ N w * ψ w) = fun w => ddv 0 R w * ψ w -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ R) w * ψ w := by
    funext w
    simp only [potQ, sub_mul, Finset.sum_mul]
    rfl
  rw [hL, hQ]
  have f1 : Integrable (fun w => -(R w * ddv 0 ψ w)) := (iR1 0).neg
  have f2 : Integrable (fun w => ∑ j : Fin 3, R w * ddv j.succ (ddv j.succ ψ) w) :=
    integrable_finsetSum _ fun j _ => iR2 j.succ
  have g2 : Integrable (fun w => ∑ j : Fin 3, ddv j.succ (ddv j.succ R) w * ψ w) :=
    integrable_finsetSum _ fun j _ => iD2 j.succ
  rw [integral_sub f1 f2, integral_sub (iD1 0) g2, integral_neg, e0,
    integral_finsetSum _ fun j _ => iR2 j.succ, integral_finsetSum _ fun j _ => iD2 j.succ]
  simp only [ej, neg_neg]

end RegularityStructures.Phi43

end
