/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.OldGamma
public import Phi43.RestartDiff.ActionDiff

/-!
# Lipschitz bound for `Γ` of two restarted canonical models

Two-model analogue of `translate_gammaMap_bound`: for two canonical renormalised models translated
by the same `a`, the shifts of the structure-group elements agree (they are coordinate
differences), so the four integrated entries bounded in difference by `Δ d^{deg}` give a bound of
all entries of `Γ_{yx} - Γ'_{yx}` by `oldGammaDiffConst A * Δ * d^{deg τ - deg σ}`.
-/

public section

namespace RegularityStructures.Phi43.Restart

private theorem eq_of_parabolicNorm_sub_eq_zero'' {x y : ParabolicSpace}
    (h : parabolicNorm (y - x) = 0) : y = x := by
  unfold parabolicNorm at h
  have h1 : 0 ≤ Real.sqrt |(y - x).1| := Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i, |(y - x).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 : Real.sqrt |(y - x).1| = 0 := by linarith
  have h4 : ∑ i, |(y - x).2 i| = 0 := by linarith
  have h5 : (y - x).1 = 0 := abs_eq_zero.1 ((Real.sqrt_eq_zero (abs_nonneg _)).1 h3)
  have h6 : ∀ i, (y - x).2 i = 0 := fun i =>
    abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h4 i
      (Finset.mem_univ i))
  exact sub_eq_zero.1 (Prod.ext h5 (funext h6))

/-- **Lipschitz bound of all entries of `Γ`** of two restarted canonical models translated by the
same `a`, from the four integrated entries. -/
theorem translate_gammaMap_bound_diff (N : ℕ) (κ : Kappa) (noise noise' : CanonicalNoise)
    (Cg Cg' : ℝ) (q q' : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise'.zeta z‖ ≤ Cg' * (1 + parabolicNorm z) ^ q')
    (C C' : RenormalisationConstants) (a : ParabolicSpace) {A Δ : ℝ} (hA : 1 ≤ A)
    (hΔ : 0 ≤ Δ) (y x : ParabolicSpace)
    (hp : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi)
    (hpg : ∀ i : Fin 3, |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) (.x i)| ≤ A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1))
    (hs : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiSq 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq)
    (hc : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiCube 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube)
    (hp₂ : |((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsi 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi)
    (hpg₂ : ∀ i : Fin 3,
      |((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsi 1) (.x i)| ≤ A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1))
    (hs₂ : |((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsiSq 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq)
    (hc₂ : |((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsiCube 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube)
    (dp : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) .one -
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsi 1) .one| ≤ Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsi)
    (dpg : ∀ i : Fin 3,
      |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) (.x i) -
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsi 1) (.x i)| ≤ Δ * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1))
    (ds : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiSq 1) .one -
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsiSq 1) .one| ≤ Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq)
    (dc : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiCube 1) .one -
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single .iPsiCube 1) .one| ≤ Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube)
    (τ σ : Symbol) (hστ : homogeneity κ σ < homogeneity κ τ) :
    |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single τ 1) σ -
      ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
        (Pi.single τ 1) σ| ≤
      oldGammaDiffConst A * Δ * parabolicNorm (y - x) ^ (homogeneity κ τ - homogeneity κ σ) := by
  by_cases hd : parabolicNorm (y - x) = 0
  · have he := eq_of_parabolicNorm_sub_eq_zero'' hd
    subst y
    have hne : τ ≠ σ := by
      intro h; subst h; exact lt_irrefl _ hστ
    rw [Model.gammaMap_self, Model.gammaMap_self]
    simp only [LinearMap.id_apply, Pi.single_apply, hne.symm, ite_false, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (oldGammaDiffConst_nonneg (by linarith)) hΔ)
      (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  · have hdpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne (parabolicNorm_nonneg _) (Ne.symm hd)
    rw [translate_gammaMap_single, translate_gammaMap_single]
    set g := (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C
      (y + a) (x + a) with hgdef
    set g' := (hairerCanonicalData (κ := κ) N noise').renormalisedExtensionGammaParameter C'
      (y + a) (x + a) with hgdef'
    have hshift (i : Fin 4) :
        |g.shift i| ≤ A * parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) := by
      have := canonicalGamma_shift_bound N κ noise (x + a) (y + a) i
      rw [add_sub_add_right_eq_sub] at this
      exact this.trans (le_mul_of_one_le_left (Real.rpow_nonneg (parabolicNorm_nonneg _) _) hA)
    have hshift' (i : Fin 4) :
        |g'.shift i| ≤ A * parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) := by
      have := canonicalGamma_shift_bound N κ noise' (x + a) (y + a) i
      rw [add_sub_add_right_eq_sub] at this
      exact this.trans (le_mul_of_one_le_left (Real.rpow_nonneg (parabolicNorm_nonneg _) _) hA)
    have hshift_eq (i : Fin 4) : g.shift i = g'.shift i := by
      have h1 : g.shift i = ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter
          (y + a) (x + a)).shift i := rfl
      have h2 : g'.shift i = ((hairerCanonicalData (κ := κ) N noise').canonicalGammaParameter
          (y + a) (x + a)).shift i := rfl
      rw [h1, h2, canonicalGamma_shift_eq_coords_sub, canonicalGamma_shift_eq_coords_sub]
    have hdx (i : Fin 4) : |g.shift i - g'.shift i| ≤
        Δ * parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) := by
      rw [hshift_eq i, sub_self, abs_zero]
      exact mul_nonneg hΔ (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
    have hp₁ : |g.cPsi| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
      rw [translate_gammaMap_single, structureBasisAction_iPsi_one] at hp
      exact hp
    have hpg₁ (i : Fin 3) : |g.cPsiGrad i| ≤
        A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
      have := hpg i
      rw [translate_gammaMap_single, structureBasisAction_iPsi_x] at this
      exact this
    have hs₁ : |g.cPsiSq| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiSq_one] at hs
      exact hs
    have hc₁ : |g.cPsiCube| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiCube_one] at hc
      exact hc
    have hp₃ : |g'.cPsi| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
      rw [translate_gammaMap_single, structureBasisAction_iPsi_one] at hp₂
      exact hp₂
    have hpg₃ (i : Fin 3) : |g'.cPsiGrad i| ≤
        A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
      have := hpg₂ i
      rw [translate_gammaMap_single, structureBasisAction_iPsi_x] at this
      exact this
    have hs₃ : |g'.cPsiSq| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiSq_one] at hs₂
      exact hs₂
    have hc₃ : |g'.cPsiCube| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiCube_one] at hc₂
      exact hc₂
    have dp' : |g.cPsi - g'.cPsi| ≤ Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
      rw [translate_gammaMap_single, translate_gammaMap_single,
        structureBasisAction_iPsi_one, structureBasisAction_iPsi_one] at dp
      exact dp
    have dpg' (i : Fin 3) : |g.cPsiGrad i - g'.cPsiGrad i| ≤
        Δ * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
      have := dpg i
      rw [translate_gammaMap_single, translate_gammaMap_single,
        structureBasisAction_iPsi_x, structureBasisAction_iPsi_x] at this
      exact this
    have ds' : |g.cPsiSq - g'.cPsiSq| ≤ Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
      rw [translate_gammaMap_single, translate_gammaMap_single,
        structureBasisAction_iPsiSq_one, structureBasisAction_iPsiSq_one] at ds
      exact ds
    have dc' : |g.cPsiCube - g'.cPsiCube| ≤
        Δ * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      rw [translate_gammaMap_single, translate_gammaMap_single,
        structureBasisAction_iPsiCube_one, structureBasisAction_iPsiCube_one] at dc
      exact dc
    exact gammaStructureBasis_weighted_bound_diff κ g g' hdpos (by linarith) hΔ hshift hp₁ hpg₁
      hs₁ hc₁ hshift' hp₃ hpg₃ hs₃ hc₃ hdx dp' dpg' ds' dc' τ σ

end RegularityStructures.Phi43.Restart

end
