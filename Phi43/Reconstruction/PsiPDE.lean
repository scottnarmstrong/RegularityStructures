/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.KernelAdjoint
public import Phi43.Structure.CanonicalConvolutionDerivative
public import Phi43.Structure.CanonicalSmoothConvolution
public import Phi43.Potential.Convolution
public import Phi43.Potential.ZetaBound
public import Phi43.Potential.KernelTail
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The heat equation for the potential `Ψ = K ∗ ζ`

`psi_pde`: `(∂_t - Δ) (K_N ∗ ζ) = ζ - Q ∗ ζ` pointwise, for a smooth space-periodic `ζ`.
Derivatives fall on `ζ` (`ddv_hairerConvolution`), and `∫ K (L ζ)(z - ·) = ζ(z) - ∫ Q ζ(z - ·)` is
`integral_hairerKernel_lstar` tested against the time-cutoff reflection `ζ̃(z - ·)` of `ζ`.
-/

public section

open Set MeasureTheory Filter RegularityStructures.Inhomogeneity RegularityStructures.Potential
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem hairerConvolution_eq_integral_swap (N : ℕ) (f : ParabolicSpace → ℝ) :
    hairerConvolution N f = fun x => ∫ w, hairerKernel N w * f (x - w) := by
  rw [hairerConvolution_eq_convolution]
  rfl

theorem integrable_hairerKernel_mul {h : ParabolicSpace → ℝ} (hh : Continuous h) (N : ℕ)
    (z : ParabolicSpace) : Integrable (fun w => hairerKernel N w * h (z - w)) := by
  have := (canonicalHairerKernel_hasCompactSupport N).convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.mul ℝ ℝ) (canonicalHairerKernel_integrable N).locallyIntegrable hh z
  exact this

theorem ddv_hairerConvolution (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 4) :
    ddv j (hairerConvolution N f) = hairerConvolution N (ddv j f) := by
  funext z
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hint : Integrable (fun w => hairerKernel N w • fderiv ℝ f (z - w)) := by
    have := (canonicalHairerKernel_hasCompactSupport N).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ParabolicSpace →L[ℝ] ℝ) →L[ℝ] (ParabolicSpace →L[ℝ] ℝ))
      (canonicalHairerKernel_integrable N).locallyIntegrable hfd z
    exact this
  simp only [ddv]
  rw [fderiv_hairerConvolution N hf z, ContinuousLinearMap.integral_apply hint,
    hairerConvolution_eq_integral_swap]
  simp [ddv]

theorem abs_fst_le_one_of_parabolicNorm_le {w : ParabolicSpace} (h : parabolicNorm w ≤ 1) :
    |w.1| ≤ 1 := by
  have h1 : Real.sqrt |w.1| ≤ 1 := by
    have : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold parabolicNorm at h
    linarith
  by_contra hlt
  have := Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) |>.2 (by nlinarith [not_le.1 hlt])
  linarith

theorem exists_time_cutoff (c : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, |x - c| ≤ 2 → χ x = 1) ∧ ∀ x, 3 ≤ |x - c| → χ x = 0 := by
  obtain ⟨χ, hχ, -, hs, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (s := Ioo (c - 3) (c + 3)) (t := Icc (c - 2) (c + 2)) isOpen_Ioo isClosed_Icc
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨χ, hχ, fun x hx => (hone x).1 (abs_le.1 hx |> fun h => ⟨by linarith [h.1], by linarith [h.2]⟩), fun x hx => ?_⟩
  by_contra hne
  have : x ∈ Function.support χ := hne
  rw [hs] at this
  have h2 : |x - c| < 3 := abs_lt.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  linarith

theorem ddv_congr_on {U : Set ParabolicSpace} (hU : IsOpen U) {F G : ParabolicSpace → ℝ}
    (h : ∀ y ∈ U, F y = G y) (j : Fin 4) : ∀ y ∈ U, ddv j F y = ddv j G y := by
  intro y hy
  have : F =ᶠ[nhds y] G := Filter.eventually_of_mem (hU.mem_nhds hy) h
  simp only [ddv, this.fderiv_eq]

theorem lstar_reflect {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (τ w : ParabolicSpace) :
    lstar (fun u => F (τ - u)) w =
      ddv 0 F (τ - w) - ∑ j : Fin 3, ddv j.succ (ddv j.succ F) (τ - w) := by
  have hd : Differentiable ℝ F := hF.differentiable (by simp)
  have hdd : ∀ j : Fin 4, Differentiable ℝ (ddv j F) := fun j =>
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have e1 : ∀ j : Fin 4, ddv j (fun u => F (τ - u)) = fun u => -ddv j F (τ - u) := by
    intro j; funext u; exact ddv_reflect hd τ j u
  have e2 : ∀ j : Fin 3, ddv j.succ (ddv j.succ (fun u => F (τ - u))) w =
      -(-ddv j.succ (ddv j.succ F) (τ - w)) := by
    intro j
    rw [e1 j.succ]
    have h1 : ddv j.succ (fun u => -ddv j.succ F (τ - u)) w =
        -ddv j.succ (fun u => ddv j.succ F (τ - u)) w :=
      ddv_neg (F := fun u => ddv j.succ F (τ - u)) _ _
    rw [h1, ddv_reflect (hdd j.succ) τ j.succ w]
  unfold lstar
  rw [e1 0]
  simp only [e2, neg_neg]

theorem perSmooth_reflect_pt {F : ParabolicSpace → ℝ} (hF : PerSmooth F) (z : ParabolicSpace) :
    PerSmooth (fun w : ParabolicSpace => F (z - w)) where
  smooth := hF.smooth.comp (contDiff_const.sub contDiff_id)
  periodic w c hc := by
    have e : z - (w.1, w.2 + c) = ((z - w).1, (z - w).2 + (-c)) := by
      ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm]
    have hc' : torusProj (-c) = 0 := by rw [RegularityStructures.PDE.torusProj_neg, hc, neg_zero]
    show F (z - (w.1, w.2 + c)) = F (z - w)
    rw [e]
    exact hF.periodic _ (-c) hc'

/-- **The heat equation for `K ∗ ζ`**: `(∂_t - Δ)(K ∗ ζ) = ζ - Q ∗ ζ`. -/
theorem psi_pde (N : ℕ) (noise : CanonicalNoise) (z : ParabolicSpace) :
    ddv 0 (hairerConvolution N noise.zeta) z -
        ∑ j : Fin 3, ddv j.succ (ddv j.succ (hairerConvolution N noise.zeta)) z =
      noise.zeta z - potConv noise.zeta (potQ N) z := by
  set ζ := noise.zeta with hζdef
  have hζ : ContDiff ℝ ∞ ζ := noise.smooth
  have hP : PerSmooth ζ := Potential.perSmooth_noise_zeta noise
  -- Step 1: derivatives fall on `ζ`
  have hd1 : ∀ j : Fin 3, ContDiff ℝ ∞ (ddv j.succ ζ) := fun j => (hP.ddv j.succ).smooth
  have e0 : ddv 0 (hairerConvolution N ζ) z = ∫ w, hairerKernel N w * ddv 0 ζ (z - w) := by
    rw [ddv_hairerConvolution N hζ 0, hairerConvolution_eq_integral_swap]
  have ej : ∀ j : Fin 3, ddv j.succ (ddv j.succ (hairerConvolution N ζ)) z =
      ∫ w, hairerKernel N w * ddv j.succ (ddv j.succ ζ) (z - w) := by
    intro j
    rw [ddv_hairerConvolution N hζ j.succ, ddv_hairerConvolution N (hd1 j) j.succ,
      hairerConvolution_eq_integral_swap]
  have iK0 : Integrable (fun w => hairerKernel N w * ddv 0 ζ (z - w)) :=
    integrable_hairerKernel_mul (hP.ddv 0).smooth.continuous N z
  have iKj : ∀ j : Fin 3, Integrable (fun w => hairerKernel N w * ddv j.succ (ddv j.succ ζ) (z - w)) :=
    fun j => integrable_hairerKernel_mul ((hP.ddv j.succ).ddv j.succ).smooth.continuous N z
  have iKs : Integrable (fun w => ∑ j : Fin 3, hairerKernel N w * ddv j.succ (ddv j.succ ζ) (z - w)) :=
    integrable_finsetSum _ fun j _ => iKj j
  have hLHS : ddv 0 (hairerConvolution N ζ) z -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ (hairerConvolution N ζ)) z =
      ∫ w, hairerKernel N w * (ddv 0 ζ (z - w) - ∑ j : Fin 3, ddv j.succ (ddv j.succ ζ) (z - w)) := by
    simp only [e0, ej]
    have : (fun w => hairerKernel N w * (ddv 0 ζ (z - w) - ∑ j : Fin 3, ddv j.succ (ddv j.succ ζ) (z - w))) =
        fun w => hairerKernel N w * ddv 0 ζ (z - w) -
          ∑ j : Fin 3, hairerKernel N w * ddv j.succ (ddv j.succ ζ) (z - w) := by
      funext w; rw [mul_sub, Finset.mul_sum]
    rw [this, integral_sub iK0 iKs, integral_finsetSum _ fun j _ => iKj j]
  rw [hLHS]
  -- Step 2: the cutoff test function
  obtain ⟨χ, hχ, hχ1, hχ0⟩ := exists_time_cutoff z.1
  set ζt : ParabolicSpace → ℝ := fun y => χ y.1 * ζ y with hζt
  have hζtP : PerSmooth ζt := ⟨(hχ.comp contDiff_fst).mul hζ, fun y c hc => by
    simp only [hζt]
    rw [hP.periodic y c hc]⟩
  set ψ : ParabolicSpace → ℝ := fun w => ζt (z - w) with hψdef
  have hψP : PerSmooth ψ := perSmooth_reflect_pt hζtP z
  have hψs : ∀ w : ParabolicSpace, 3 < |w.1| → ψ w = 0 := by
    intro w hw
    simp only [hψdef, hζt]
    rw [hχ0 _ (by simp; exact hw.le), zero_mul]
  have hF3 := integral_hairerKernel_lstar N hψP (by norm_num : (0 : ℝ) ≤ 3) hψs
  -- support facts
  have hsupK : ∀ w : ParabolicSpace, hairerKernel N w ≠ 0 → |w.1| ≤ 1 := by
    intro w hw
    refine abs_fst_le_one_of_parabolicNorm_le (not_lt.1 fun h => hw ?_)
    exact hairerKernel_eq_zero_of_one_lt N h
  have hsupQ : ∀ w : ParabolicSpace, potQ N w ≠ 0 → |w.1| ≤ 1 := by
    intro w hw
    refine abs_fst_le_one_of_parabolicNorm_le (not_lt.1 fun h => hw ?_)
    exact potQ_eq_zero_of_one_lt N h
  -- the local agreement of `ζt` and `ζ`
  have hU : IsOpen {y : ParabolicSpace | |y.1 - z.1| < 2} :=
    isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
  have hagree : ∀ y ∈ {y : ParabolicSpace | |y.1 - z.1| < 2}, ζt y = ζ y := by
    intro y hy
    simp only [hζt]
    rw [hχ1 _ (le_of_lt hy), one_mul]
  have hL : ∀ y ∈ {y : ParabolicSpace | |y.1 - z.1| < 2},
      ddv 0 ζt y - ∑ j : Fin 3, ddv j.succ (ddv j.succ ζt) y =
        ddv 0 ζ y - ∑ j : Fin 3, ddv j.succ (ddv j.succ ζ) y := by
    intro y hy
    rw [ddv_congr_on hU hagree 0 y hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact ddv_congr_on hU (ddv_congr_on hU hagree j.succ) j.succ y hy
  have hint1 : (∫ w, hairerKernel N w * (ddv 0 ζ (z - w) -
      ∑ j : Fin 3, ddv j.succ (ddv j.succ ζ) (z - w))) = ∫ w, hairerKernel N w * lstar ψ w := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : hairerKernel N w = 0
    · beta_reduce; rw [hw, zero_mul, zero_mul]
    · have h1 := hsupK w hw
      have hζtc : ContDiff ℝ ∞ ζt := hζtP.smooth
      simp only [hψdef]
      rw [lstar_reflect hζtc z w]
      congr 1
      rw [hL (z - w) (by
        show |(z - w).1 - z.1| < 2
        simp only [Prod.fst_sub, sub_sub_cancel_left, abs_neg]
        linarith)]
  rw [hint1, hF3]
  -- the right-hand side
  have hψ0 : ψ 0 = ζ z := by
    simp only [hψdef, hζt, sub_zero]
    rw [hχ1 z.1 (by simp), one_mul]
  have hQint : (∫ w, potQ N w * ψ w) = ∫ w, potQ N w * ζ (z - w) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : potQ N w = 0
    · beta_reduce; rw [hw, zero_mul, zero_mul]
    · have h1 := hsupQ w hw
      simp only [hψdef, hζt]
      rw [hχ1 _ (by simp; linarith), one_mul]
  have hconv : potConv ζ (potQ N) z = ∫ w, potQ N w * ζ (z - w) := by
    unfold potConv
    have : (volume : Measure ParabolicSpace).IsNegInvariant := by
      rw [Measure.volume_eq_prod]
      refine ⟨?_⟩
      have h := Measure.map_prod_map (volume : Measure ℝ) (volume : Measure (Fin 3 → ℝ))
        (measurable_neg (G := ℝ)) (measurable_neg (G := Fin 3 → ℝ))
      rw [Measure.map_neg_eq_self, Measure.map_neg_eq_self] at h
      exact h.symm
    have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
      rw [Measure.volume_eq_prod]; infer_instance
    rw [← integral_sub_left_eq_self (fun y : ParabolicSpace => ζ y * potQ N (z - y))
      (volume : Measure ParabolicSpace) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [sub_sub_cancel]
    ring
  rw [hψ0, hQint, hconv]

end RegularityStructures.Phi43

end
