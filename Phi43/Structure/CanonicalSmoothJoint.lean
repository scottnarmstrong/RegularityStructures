/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothCancellation
public import Phi43.Structure.CanonicalSmoothCharacters
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Joint smoothness and compact cancellation bounds

Hairer [Hai14, Proposition 8.27]. The actual canonical functions are smooth
jointly in base point and evaluation point. On a compact set the positive
symbols have a uniform first-order cancellation bound. These local results
do not impose temporal growth conditions.
-/

public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff in
private theorem coord_smooth (i : Fin 4) :
    ContDiff ℝ ∞ (fun z : ParabolicSpace => parabolicCoords z i) := by
  fin_cases i
  · exact contDiff_fst
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 2)
    fun_prop

open scoped ContDiff in
private theorem gradient_smooth (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (hairerSpatialGradient N f i) := by
  have he : hairerSpatialGradient N f i =
      fun z => fderiv ℝ (hairerConvolution N f) z (0, Pi.single i 1) :=
    funext (hairerSpatialGradient_eq_fderiv N hf i)
  rw [he]
  exact ((contDiff_hairerConvolution N hf).fderiv_right (by simp)).clm_apply contDiff_const

open scoped ContDiff in
private theorem integrate_joint_smooth (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (r : ℝ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N noise).integrate r f p.1 p.2) := by
  have hc := contDiff_hairerConvolution N hf
  have hg := gradient_smooth N hf
  have hcoord := coord_smooth
  simp only [CanonicalData.integrate, CanonicalKernel.convolution,
    CanonicalKernel.taylorPolynomial, hairerCanonicalData, hairerCanonicalKernel]
  split_ifs <;> fun_prop

open scoped ContDiff in
/-- Smoothness in both arguments of every actual retained canonical function. -/
theorem canonicalPi_joint_smooth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (τ : Symbol) :
    ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N noise).canonicalPi p.1 (basis τ) p.2) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hp : ContDiff ℝ ∞ D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hs : ContDiff ℝ ∞ D.localPsiSq := hp.mul hp
  have hc : ContDiff ℝ ∞ D.localPsiCube := hs.mul hp
  have hi := integrate_joint_smooth N κ noise (homogeneity κ .iPsi) hp
  have his := integrate_joint_smooth N κ noise (homogeneity κ .iPsiSq) hs
  have hic := integrate_joint_smooth N κ noise (homogeneity κ .iPsiCube) hc
  have hrel (i : Fin 4) : ContDiff ℝ ∞
      (fun p : ParabolicSpace × ParabolicSpace => CanonicalData.relCoord p.1 p.2 i) :=
    ((coord_smooth i).comp contDiff_snd).sub ((coord_smooth i).comp contDiff_fst)
  simp_rw [CanonicalData.canonicalPi_basis]
  change ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
    D.localPiBasis p.1 τ p.2)
  cases τ with
  | one => exact contDiff_const
  | noise => exact noise.smooth.comp contDiff_snd
  | x0 => exact hrel 0
  | x i => exact hrel i.succ
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      exact (hrel i.succ).mul (hrel j.succ)
  | psi => exact hp.comp contDiff_snd
  | psiSq => exact hs.comp contDiff_snd
  | psiCube => exact hc.comp contDiff_snd
  | psiX i => exact (hp.comp contDiff_snd).mul (hrel i.succ)
  | psiSqX i => exact (hs.comp contDiff_snd).mul (hrel i.succ)
  | iPsi => exact hi
  | iPsiSq => exact his
  | iPsiCube => exact hic
  | iPsiPsi => exact hi.mul (hp.comp contDiff_snd)
  | iPsiPsiSq => exact hi.mul (hs.comp contDiff_snd)
  | iPsiSqPsi => exact his.mul (hp.comp contDiff_snd)
  | iPsiSqPsiSq => exact his.mul (hs.comp contDiff_snd)
  | iPsiCubePsi => exact hic.mul (hp.comp contDiff_snd)
  | iPsiCubePsiSq => exact hic.mul (hs.comp contDiff_snd)
  | iPsiCubeSq => exact hic.mul hic

/-- The positive canonical sector has a uniform first-order cancellation
bound on every compact set, derived from the smooth noise. -/
theorem canonicalPi_positive_compact_lipschitz (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : Symbol, 0 < homogeneity κ τ →
      ∀ x ∈ S, ∀ y ∈ S,
        |(hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) y| ≤
          C * ‖y - x‖ := by
  obtain ⟨R, hR⟩ := (hS.prod hS).isBounded.subset_closedBall
    (0 : ParabolicSpace × ParabolicSpace)
  have hb (τ : Symbol) : ∃ B : NNReal, LipschitzOnWith B
      (fun p : ParabolicSpace × ParabolicSpace =>
        (hairerCanonicalData (κ := κ) N noise).canonicalPi p.1 (basis τ) p.2)
      (Metric.closedBall 0 R) :=
    (canonicalPi_joint_smooth N κ noise τ).contDiffOn.exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose B hB using hb
  refine ⟨∑ τ : Symbol, (B τ : ℝ), Finset.sum_nonneg (fun τ _ => (B τ).coe_nonneg), ?_⟩
  intro τ hτ x hx y hy
  have hh := (hB τ).dist_le_mul (x, y) (hR ⟨hx, hy⟩) (x, x) (hR ⟨hx, hx⟩)
  have he : dist (x, y) (x, x) = ‖y - x‖ := by
    simp [dist_eq_norm]
  rw [canonicalPi_positive_at_base N κ noise τ hτ x, he, Real.dist_eq, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun σ _ => (B σ).coe_nonneg) (Finset.mem_univ τ))
    (norm_nonneg _))

end RegularityStructures.Phi43

end
