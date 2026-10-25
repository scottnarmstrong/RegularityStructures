/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionBasedForm
public import Phi43.Structure.CanonicalSmoothJoint

/-!
# Joint smoothness and diagonal cancellation of the corrected lift

These follow from the actual based formulas, including the corrected
integrated-cubic square, and supply the local positive-sector analytic
ingredient [Hai14, Proposition 8.27, Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff in
theorem renormalisedExtensionPi_joint_smooth (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (τ : Symbol) :
    ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C p.1 (basis τ) p.2) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hl (τ : Symbol) : ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
      D.localPiBasis p.1 τ p.2) := by
    simpa only [CanonicalData.canonicalPi_basis] using canonicalPi_joint_smooth N κ noise τ
  have hg (τ : Symbol) := canonicalGlobalPiBasis_smooth N (κ := κ) noise τ
  have hs : ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace => D.globalPsiSq p.2 - C₁ C) :=
    ((hg .psiSq).comp contDiff_snd).sub contDiff_const
  have hp : ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace => D.globalPsi p.2) :=
    (hg .psi).comp contDiff_snd
  have hpot : ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
      D.renormalisedBasedCube C p.1 p.2) :=
    (hl .iPsiCube).sub (contDiff_const.mul
      (((hg .iPsi).comp contDiff_snd).sub ((hg .iPsi).comp contDiff_fst)))
  simp_rw [renormalisedExtensionPi_basis_form]
  change ContDiff ℝ ∞ (fun p : ParabolicSpace × ParabolicSpace =>
    D.renormalisedBasedBasis C p.1 τ p.2)
  cases τ with
  | psiSq => exact hs
  | psiCube => exact ((hg .psiCube).comp contDiff_snd).sub (contDiff_const.mul hp)
  | psiSqX i => exact hs.mul (hl (.x i))
  | iPsiCube => exact hpot
  | iPsiPsiSq => exact (hl .iPsi).mul hs
  | iPsiSqPsiSq => exact ((hl .iPsiSq).mul hs).sub contDiff_const
  | iPsiCubePsi => exact hpot.mul hp
  | iPsiCubePsiSq => exact (hpot.mul hs).sub (contDiff_const.mul hp)
  | iPsiCubeSq => exact hpot.mul hpot
  | one => exact hl .one
  | noise => exact hl .noise
  | x0 => exact hl .x0
  | x i => exact hl (.x i)
  | xMul q => exact hl (.xMul q)
  | psi => exact hl .psi
  | iPsi => exact hl .iPsi
  | psiX i => exact hl (.psiX i)
  | iPsiSq => exact hl .iPsiSq
  | iPsiPsi => exact hl .iPsiPsi
  | iPsiSqPsi => exact hl .iPsiSqPsi

/-- All positive retained corrected trees vanish at their base point. -/
theorem renormalisedExtensionPi_positive_at_base (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (τ : Symbol) (hτ : 0 < homogeneity κ τ)
    (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) x = 0 := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hz (σ : Symbol) (hσ : 0 < homogeneity κ σ) : D.localPiBasis x σ x = 0 := by
    simpa only [CanonicalData.canonicalPi_basis] using canonicalPi_positive_at_base N κ noise σ hσ x
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hk0 : 0 < κ.1 := κ.2.1
  have hi : D.localIPsi x x = 0 := hz .iPsi (by simp only [homogeneity]; linarith)
  have hc : D.localIPsiCube x x = 0 := hz .iPsiCube (by simp only [homogeneity]; linarith)
  rw [renormalisedExtensionPi_basis_form]
  change D.renormalisedBasedBasis C x τ x = 0
  cases τ <;> first | exact hz _ hτ | skip
  all_goals simp only [homogeneity] at hτ
  all_goals try (exfalso; linarith)
  all_goals simp [CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube, hi, hc]

/-- Uniform compact Lipschitz cancellation, derived from joint smoothness. -/
theorem renormalisedExtensionPi_positive_compact_lipschitz (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : Symbol, 0 < homogeneity κ τ → ∀ x ∈ S, ∀ y ∈ S,
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y| ≤
        B * ‖y - x‖ := by
  obtain ⟨R, hR⟩ := (hS.prod hS).isBounded.subset_closedBall
    (0 : ParabolicSpace × ParabolicSpace)
  have hb (τ : Symbol) : ∃ B : NNReal, LipschitzOnWith B
      (fun p : ParabolicSpace × ParabolicSpace =>
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C p.1 (basis τ) p.2)
      (Metric.closedBall 0 R) :=
    (renormalisedExtensionPi_joint_smooth N κ noise C τ).contDiffOn.exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose B hB using hb
  refine ⟨∑ τ : Symbol, (B τ : ℝ), Finset.sum_nonneg (fun τ _ => (B τ).coe_nonneg), ?_⟩
  intro τ hτ x hx y hy
  have hh := (hB τ).dist_le_mul (x, y) (hR ⟨hx, hy⟩) (x, x) (hR ⟨hx, hx⟩)
  have he : dist (x, y) (x, x) = ‖y - x‖ := by simp [dist_eq_norm]
  rw [renormalisedExtensionPi_positive_at_base N κ noise C τ hτ x, he,
    Real.dist_eq, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun σ _ => (B σ).coe_nonneg) (Finset.mem_univ τ)) (norm_nonneg _))

end RegularityStructures.Phi43

end
