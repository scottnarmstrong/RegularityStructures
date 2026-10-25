/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedGammaLocal
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.CanonicalGammaPrimitiveBounds
public import RegularityStructures.Abstract.Model

/-!
# Compact Gamma bounds of the genuine corrected smooth Model

The local multiplicative bounds and actual joint character continuity give
the full compact estimate [Hai14, Theorem 8.44]. No analytic-bound data are
assumed.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- Continuity of every actual corrected transition matrix coefficient. -/
theorem continuous_renormalisedGamma_coeff (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (R : RenormalisationConstants) (τ σ : Symbol) :
    Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma R p.2 p.1 (basis τ)) σ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  let g : ParabolicSpace × ParabolicSpace → G := fun p => D.renormalisedExtensionGammaParameter R p.2 p.1
  have hcoord (i : Fin 4) : Continuous (fun z : ParabolicSpace => parabolicCoords z i) := by
    fin_cases i
    · exact continuous_fst
    · change Continuous (fun z : ParabolicSpace => z.2 0)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 1)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 2)
      fun_prop
  have hx (i : Fin 4) : Continuous (fun p => (g p).shift i) := by
    have he : (fun p => (g p).shift i) = fun p : ParabolicSpace × ParabolicSpace =>
        parabolicCoords p.2 i - parabolicCoords p.1 i :=
      funext fun p => canonicalGamma_shift_eq_coords_sub N κ noise p.1 p.2 i
    rw [he]
    exact ((hcoord i).comp continuous_snd).sub ((hcoord i).comp continuous_fst)
  have hp : Continuous (fun p => (g p).cPsi) := by
    have he : (fun p => (g p).cPsi) = fun p : ParabolicSpace × ParabolicSpace =>
        D.canonicalPi p.1 (basis .iPsi) p.2 :=
      funext fun p => canonicalGamma_cPsi_eq_iPsi N κ noise p.1 p.2
    rw [he]
    exact (canonicalPi_joint_smooth N κ noise .iPsi).continuous
  have hps : ContDiff ℝ (↑(⊤ : ℕ∞)) D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hg (i : Fin 3) : Continuous (fun p => (g p).cPsiGrad i) := by
    have he : (fun p => (g p).cPsiGrad i) = fun p : ParabolicSpace × ParabolicSpace =>
        hairerSpatialGradient N D.localPsi i p.2 - hairerSpatialGradient N D.localPsi i p.1 :=
      funext fun p => canonicalGamma_cPsiGrad_eq_gradient_sub N κ noise p.1 p.2 i
    rw [he]
    exact ((continuous_hairerSpatialGradient N hps i).comp continuous_snd).sub
      ((continuous_hairerSpatialGradient N hps i).comp continuous_fst)
  have hs : Continuous (fun p => (g p).cPsiSq) := by
    have he : (fun p => (g p).cPsiSq) = fun p : ParabolicSpace × ParabolicSpace =>
        D.canonicalPi p.1 (basis .iPsiSq) p.2 :=
      funext fun p => canonicalGamma_cPsiSq_eq_iPsiSq N κ noise p.1 p.2
    rw [he]
    exact (canonicalPi_joint_smooth N κ noise .iPsiSq).continuous
  have hc : Continuous (fun p => (g p).cPsiCube) := by
    have he : (fun p => (g p).cPsiCube) = fun p : ParabolicSpace × ParabolicSpace =>
        D.renormalisedExtensionPi R p.1 (basis .iPsiCube) p.2 :=
      funext fun p => renormalisedGamma_cPsiCube_eq N κ noise R p.1 p.2
    rw [he]
    exact (renormalisedExtensionPi_joint_smooth N κ noise R .iPsiCube).continuous
  exact continuous_structureGroupMap_basis g hx hp hg hs hc τ σ

/-- The compact Gamma estimate for every retained symbol below the fixed-point
cutoff. This proves the Gamma bound for the renormalised model
[Hai14, Theorem 8.44] on the retained sector, without any temporal growth
hypothesis. -/
theorem renormalisedGamma_compact_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (R : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ σ : Symbol,
      homogeneity κ τ < gamma κ → homogeneity κ σ < homogeneity κ τ →
      ∀ x ∈ S, ∀ y ∈ S,
        |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma R y x (basis τ)) σ| ≤
          C * parabolicNorm (y - x) ^ (homogeneity κ τ - homogeneity κ σ) := by
  obtain ⟨C, hC0, hC⟩ := renormalisedGamma_local_bound N κ noise R hS
  have hb (τ σ : Symbol) : ∃ B : ℝ, ∀ p ∈ S ×ˢ S,
      |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma R p.2 p.1 (basis τ)) σ| ≤ B := by
    obtain ⟨B, hB⟩ := (hS.prod hS).exists_bound_of_continuousOn
      (continuous_renormalisedGamma_coeff N κ noise R τ σ).continuousOn
    exact ⟨B, fun p hp => by simpa only [Real.norm_eq_abs] using hB p hp⟩
  choose B hB using hb
  let D : ℝ := ∑ τ : Symbol, ∑ σ : Symbol, max (B τ σ) 0
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun τ _ =>
    Finset.sum_nonneg fun σ _ => le_max_right _ _
  have hBD (τ σ : Symbol) : B τ σ ≤ D :=
    (le_max_left _ _).trans ((Finset.single_le_sum (fun υ _ => le_max_right (B τ υ) 0)
      (Finset.mem_univ σ)).trans (Finset.single_le_sum
        (fun υ _ => Finset.sum_nonneg fun ω _ => le_max_right (B υ ω) 0) (Finset.mem_univ τ)))
  refine ⟨max C D, hC0.trans (le_max_left _ _), fun τ σ _hτγ hστ x hx y hy => ?_⟩
  by_cases hxy : parabolicNorm (y - x) ≤ 1
  · exact (hC τ σ hστ x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
  · have hd : 1 ≤ parabolicNorm (y - x) := (lt_of_not_ge hxy).le
    exact ((hB τ σ (x, y) ⟨hx, hy⟩).trans (hBD τ σ)).trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right (hD0.trans (le_max_right _ _))
        (Real.one_le_rpow hd (sub_pos.2 hστ).le)))

/-- Full compact Gamma bounds under the explicit polynomial growth bound on
the first four derivatives of the noise. -/
theorem canonicalRenormalisedModel_gamma_bounds (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧
      (canonicalRenormalisedModel N κ noise Cg q hg C).GammaBoundOn (gamma κ) B S := by
  obtain ⟨B, hB0, hB⟩ := renormalisedGamma_compact_bound N κ noise C hS
  refine ⟨B, hB0, fun τ σ hτ hσ x hx y hy => ?_⟩
  change |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma C y x
    (phi43CoordinateEquiv.symm (Pi.single τ 1))) σ| ≤ _
  have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  rw [he]
  exact hB τ σ hτ hσ x hx y hy

end RegularityStructures.Phi43

end

