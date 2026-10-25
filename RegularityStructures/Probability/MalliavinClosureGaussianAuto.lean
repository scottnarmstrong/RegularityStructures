/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureGaussianIBP
public import RegularityStructures.Probability.MalliavinClosureGaussianData
public import RegularityStructures.Probability.MalliavinClosureDuality

set_option linter.style.haveILetI false

/-!
# Automatic integrability for finite-dimensional Gaussian IBP

The finite-dimensional integration-by-parts theorem keeps its analytic assumptions explicit.  For
the closure argument, those assumptions follow from a `C¹` polynomial bound, both before and after
the covariance square-root map.  This module proves that conversion once, including the Lebesgue
density hypotheses needed by the one-dimensional Stein step.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

private lemma malliavin_auto_coordinate_bound {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    {C : ℝ} {M : ℕ} (_hC : 0 ≤ C)
    (hg : ∀ x : Fin N → ℝ,
      |g x| + ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ M)
    (i : Fin N) : ∀ x : Fin N → ℝ,
      |coordinateDerivative g i x| ≤ C * (1 + ‖x‖) ^ M := by
  intro x
  have hnorm : ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ ‖fderiv ℝ g x‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ g x) (Pi.single i 1)
    have hs : ‖(Pi.single i (1 : ℝ) : Fin N → ℝ)‖ = 1 := by
      classical
      rw [Pi.norm_single]
      simp
    simpa [hs] using h
  have hsum : ‖fderiv ℝ g x‖ ≤ |g x| + ‖fderiv ℝ g x‖ :=
    le_add_of_nonneg_left (abs_nonneg _)
  have h := hnorm.trans (hsum.trans (hg x))
  simpa [coordinateDerivative, Real.norm_eq_abs] using h

private lemma malliavin_auto_coordinate_mul_bound {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    {C : ℝ} {M : ℕ} (hC : 0 ≤ C)
    (hg : ∀ x : Fin N → ℝ,
      |g x| ≤ C * (1 + ‖x‖) ^ M)
    (i : Fin N) : ∀ x : Fin N → ℝ,
      |x i * g x| ≤ C * (1 + ‖x‖) ^ (M + 1) := by
  intro x
  have hxi : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i)
  have hr : 0 ≤ 1 + ‖x‖ := by positivity
  have hnorm : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  have hp : 0 ≤ (1 + ‖x‖) ^ M := pow_nonneg hr _
  calc
    |x i * g x| = |x i| * |g x| := abs_mul _ _
    _ ≤ ‖x‖ * (C * (1 + ‖x‖) ^ M) := by
      exact mul_le_mul hxi (hg x) (abs_nonneg _) (by positivity)
    _ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ M) := by
      exact mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ = C * (1 + ‖x‖) ^ (M + 1) := by
      rw [pow_succ]
      ring

private lemma malliavin_auto_transformed_coordinate_bound {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {C : ℝ} {M : ℕ} (_hC : 0 ≤ C)
    (hg : ∀ z : Fin N → ℝ,
      |g (Matrix.mulVec A z)| +
          ‖fderiv ℝ (fun y => g (Matrix.mulVec A y)) z‖ ≤ C * (1 + ‖z‖) ^ M)
    : ∀ z : Fin N → ℝ,
      |g (Matrix.mulVec A z)| ≤ C * (1 + ‖z‖) ^ M := by
  intro z
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hg z)

theorem malliavin_gaussian_ibp_of_polynomial_growth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {Y : Ω → Fin N → ℝ} {C A : Matrix (Fin N) (Fin N) ℝ}
    {g : (Fin N → ℝ) → ℝ}
    (hY : IsCentredGaussianVector P Y C)
    (hAsymm : A.IsSymm) (hAsq : A * A = C)
    (hlaw : P.map Y = (standardGaussianMeasure N).map
      (Matrix.mulVecLin A))
    (hcont : ContDiff ℝ 1 g)
    (hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin N → ℝ, |g x| + ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_trans : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin N → ℝ, |g (Matrix.mulVec A z)| +
        ‖fderiv ℝ (fun y => g (Matrix.mulVec A y)) z‖ ≤
          K * (1 + ‖z‖) ^ M) :
    ∀ j, ∫ ω, Y ω j * g (Y ω) ∂P =
      ∑ i, C j i * ∫ ω, coordinateDerivative g i (Y ω) ∂P := by
  let L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap
  letI : IsGaussian (P.map Y) := hY.2.1
  letI : IsGaussian (standardGaussianMeasure N) := isGaussian_standardGaussianMeasure N
  letI : IsProbabilityMeasure (standardGaussianMeasure N) := by
    dsimp [standardGaussianMeasure]
    infer_instance
  have hLmeas : AEMeasurable (Matrix.mulVecLin A)
      (standardGaussianMeasure N) :=
    L.continuous.measurable.aemeasurable
  have hcoord_cont (i : Fin N) :
      Continuous (fun x => coordinateDerivative g i x) := by
    have h := hcont.continuous_fderiv_apply one_ne_zero
    simpa [coordinateDerivative, Function.comp_def] using h.comp
      (by fun_prop : Continuous (fun x : Fin N → ℝ => (x, Pi.single i 1)))
  rcases hgrowth with ⟨K, M, hK, hgrowth⟩
  rcases hgrowth_trans with ⟨K', M', hK', hgrowth_trans⟩
  have hgrowth_full : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin N → ℝ, |g x| + ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ M :=
    ⟨K, M, hK, hgrowth⟩
  have hgrowth_trans_full : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin N → ℝ, |g (Matrix.mulVec A z)| +
        ‖fderiv ℝ (fun y => g (Matrix.mulVec A y)) z‖ ≤
          K * (1 + ‖z‖) ^ M :=
    ⟨K', M', hK', hgrowth_trans⟩
  have hgrowth_value : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin N → ℝ, |g x| ≤ K * (1 + ‖x‖) ^ M :=
    ⟨K, M, hK, fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hgrowth x)⟩
  have hmem_g_map : MemLp g 2 (P.map Y) :=
    memLp_of_polynomial_bound_gaussian hcont.continuous.measurable.aestronglyMeasurable
      hgrowth_value
  have hmem_deriv_map (i : Fin N) :
      MemLp (coordinateDerivative g i) 2 (P.map Y) :=
    memLp_of_polynomial_bound_gaussian (hcoord_cont i).measurable.aestronglyMeasurable
      ⟨K, M, hK, malliavin_auto_coordinate_bound hK hgrowth i⟩
  have hmem_xg_map (i : Fin N) :
      MemLp (fun x : Fin N → ℝ => x i * g x) 2 (P.map Y) := by
    have hmeas : AEStronglyMeasurable (fun x : Fin N → ℝ => x i * g x) (P.map Y) :=
      ((measurable_pi_apply i).mul hcont.continuous.measurable).aestronglyMeasurable
    exact memLp_of_polynomial_bound_gaussian hmeas
      ⟨K, M + 1, hK, malliavin_auto_coordinate_mul_bound hK
        (fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hgrowth x)) i⟩
  have hint_g : Integrable (fun ω => g (Y ω)) P :=
    (hmem_g_map.comp_of_map hY.1).integrable (by norm_num)
  have hint_deriv (i : Fin N) : Integrable
      (fun ω => coordinateDerivative g i (Y ω)) P :=
    (hmem_deriv_map i |>.comp_of_map hY.1).integrable (by norm_num)
  have hint_xg (i : Fin N) : Integrable
      (fun ω => Y ω i * g (Y ω)) P :=
    (hmem_xg_map i |>.comp_of_map hY.1).integrable (by norm_num)
  have hmem_g_stdmap : MemLp g 2
      ((standardGaussianMeasure N).map (Matrix.mulVecLin A)) := by
    rw [← hlaw]
    exact hmem_g_map
  have hmem_deriv_stdmap (i : Fin N) : MemLp (coordinateDerivative g i) 2
      ((standardGaussianMeasure N).map (Matrix.mulVecLin A)) := by
    rw [← hlaw]
    exact hmem_deriv_map i
  have hmem_g_std : MemLp (fun z : Fin N → ℝ => g (Matrix.mulVec A z)) 2
      (standardGaussianMeasure N) := by
    simpa [L, Function.comp_def] using hmem_g_stdmap.comp_of_map hLmeas
  have hmem_deriv_std (i : Fin N) : MemLp
      (fun z : Fin N → ℝ => coordinateDerivative g i (Matrix.mulVec A z)) 2
        (standardGaussianMeasure N) := by
    simpa [L, Function.comp_def] using (hmem_deriv_stdmap i).comp_of_map hLmeas
  have hint_g_std : Integrable
      (fun z : Fin N → ℝ => g (Matrix.mulVec A z)) (standardGaussianMeasure N) :=
    hmem_g_std.integrable (by norm_num)
  have hint_deriv_std (i : Fin N) : Integrable
      (fun z : Fin N → ℝ => coordinateDerivative g i (Matrix.mulVec A z))
        (standardGaussianMeasure N) :=
    (hmem_deriv_std i).integrable (by norm_num)
  have hgrowth_trans_value : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin N → ℝ, |g (Matrix.mulVec A z)| ≤ K * (1 + ‖z‖) ^ M :=
    ⟨K', M', hK', fun z => (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hgrowth_trans z)⟩
  have hint_xg_std (i : Fin N) : Integrable
      (fun z : Fin N → ℝ => z i * g (Matrix.mulVec A z))
        (standardGaussianMeasure N) := by
    have hmeas : AEStronglyMeasurable
        (fun z : Fin N → ℝ => z i * g (Matrix.mulVec A z))
        (standardGaussianMeasure N) := by
      exact ((measurable_pi_apply i).mul
        (hcont.comp L.contDiff).continuous.measurable).aestronglyMeasurable
    have hm := memLp_of_polynomial_bound_gaussian hmeas
      ⟨K', M' + 1, hK', malliavin_auto_coordinate_mul_bound hK'
        (fun z => (le_add_of_nonneg_right (norm_nonneg _)).trans
          (hgrowth_trans z)) i⟩
    exact hm.integrable (by norm_num)
  have hint_g_density : Integrable
      (fun z : Fin N → ℝ => g (Matrix.mulVec A z) * standardGaussianDensityReal z)
        (volume : Measure (Fin N → ℝ)) :=
    malliavin_integrable_standardGaussian_density hint_g_std
  have hint_deriv_density (i : Fin N) : Integrable
      (fun z : Fin N → ℝ => coordinateDerivative g i (Matrix.mulVec A z) *
        standardGaussianDensityReal z) (volume : Measure (Fin N → ℝ)) :=
    malliavin_integrable_standardGaussian_density (hint_deriv_std i)
  have hint_xg_density (i : Fin N) : Integrable
      (fun z : Fin N → ℝ => z i * g (Matrix.mulVec A z) *
        standardGaussianDensityReal z) (volume : Measure (Fin N → ℝ)) :=
    malliavin_integrable_standardGaussian_density (hint_xg_std i)
  exact gaussian_vector_integration_by_parts_of_standard_representation hY hAsymm hAsq
    hlaw hcont hgrowth_full hgrowth_trans_full hint_g hint_deriv hint_xg hint_g_std hint_deriv_std
    hint_xg_std hint_g_density hint_deriv_density hint_xg_density

theorem malliavin_cylindrical_ibp_of_polynomial_growth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
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
    (hgrowth_trans : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin (n + 1) → ℝ,
        |malliavinTailLift f (Matrix.mulVec A z)| +
          ‖fderiv ℝ (fun y => malliavinTailLift f (Matrix.mulVec A y)) z‖ ≤
            K * (1 + ‖z‖) ^ M)
    (hY_zero : ∀ ω, Y ω 0 = W k ω)
    (hY_succ : ∀ (ω : Ω) (i : Fin n), Y ω i.succ = W (h i) ω)
    (hB : ∀ i : Fin n, B 0 i.succ = ∫ z, k z * h i z) :
    ∫ ω, f (fun i => W (h i) ω) * W k ω ∂P =
      ∑ i, (∫ ω, coordinateDerivative f i (fun j => W (h j) ω) ∂P) *
        (∫ z, h i z * k z) := by
  have hparts := malliavin_gaussian_ibp_of_polynomial_growth
    (g := malliavinTailLift f) hY hAsymm hAsq hlaw
    (hcont_f.comp (malliavinTailCLM n).contDiff) hgrowth_tail hgrowth_trans
  have hparts0 := hparts 0
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
  have hleft : ∫ ω, Y ω 0 * malliavinTailLift f (Y ω) ∂P =
      ∫ ω, f (fun i => W (h i) ω) * W k ω ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hY_zero, malliavinTailLift_apply]
    have htail : (fun i => Y ω i.succ) = (fun i => W (h i) ω) := by
      funext i
      rw [hY_succ]
    rw [htail]
    ring
  rw [hleft] at hparts0
  rw [Fin.sum_univ_succ, hzero] at hparts0
  simp only [mul_zero, zero_add] at hparts0
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
  rw [hsum] at hparts0
  exact hparts0

end RegularityStructures

end
