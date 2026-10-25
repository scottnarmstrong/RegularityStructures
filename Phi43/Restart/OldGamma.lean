/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Periodic
public import Phi43.Pinned.GroupParameters
public import Phi43.Structure.CanonicalGammaActionBounds
public import Phi43.Structure.CanonicalGammaPrimitiveBounds

/-!
# `Γ` of the restarted canonical model from four primitive entries

The structure group of the old structure is parametrised by `shift`, `cPsi`, `cPsiGrad`, `cPsiSq`,
`cPsiCube`, which are entries of `Γ e_{X_i}`, `Γ e_{I(Ψ)}`, `Γ e_{I(Ψ²)}`, `Γ e_{I(Ψ³)}`.  The shifts
are coordinate differences; given the four integrated entries bounded by `A d^{deg}`, all entries of
`Γ_{yx}` of the restarted canonical model obey the bounds `C(A) d^{deg τ - deg σ}`
(`gammaStructureBasis_weighted_bound`, `C(A) = oldGammaConst A`).
-/

public section

namespace RegularityStructures.Phi43.Restart

/-- The constant of the bound of all entries of `Γ` in terms of the primitive constant `A`. -/
@[expose] def oldGammaConst (A : ℝ) : ℝ :=
  (1 + 4 * A) + (Fintype.card Symbol : ℝ) ^ 2 * (1 + 4 * A) ^ 2 +
    ((Fintype.card Symbol : ℝ) ^ 2) ^ 2 * (1 + 4 * A) ^ 3

theorem oldGammaConst_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ oldGammaConst A := by
  unfold oldGammaConst; positivity

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  (C : RenormalisationConstants) (a : ParabolicSpace)

/-- The entries of `Γ` of the translated canonical model are those of the structure-group element
of the corrected transition parameter. -/
theorem translate_gammaMap_single (y x : ParabolicSpace) (τ σ : Symbol) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x (Pi.single τ 1) σ =
      structureBasisAction ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter
        C (y + a) (x + a)) τ σ := by
  change (((phi43StructureGroupElement
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C (y + a) (x + a)) :
      LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ)) : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single τ 1)) σ = _
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  rfl

private theorem eq_of_parabolicNorm_sub_eq_zero' {x y : ParabolicSpace}
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

/-- **All entries of `Γ`** of the restarted canonical model from the four integrated entries. -/
theorem translate_gammaMap_bound {A : ℝ} (hA : 1 ≤ A) (y x : ParabolicSpace)
    (hp : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi)
    (hpg : ∀ i : Fin 3, |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsi 1) (.x i)| ≤ A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1))
    (hs : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiSq 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq)
    (hc : |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single .iPsiCube 1) .one| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube)
    (τ σ : Symbol) (hστ : homogeneity κ σ < homogeneity κ τ) :
    |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
        (Pi.single τ 1) σ| ≤
      oldGammaConst A * parabolicNorm (y - x) ^ (homogeneity κ τ - homogeneity κ σ) := by
  by_cases hd : parabolicNorm (y - x) = 0
  · have he := eq_of_parabolicNorm_sub_eq_zero' hd
    subst y
    have hne : τ ≠ σ := by
      intro h; subst h; exact lt_irrefl _ hστ
    rw [Model.gammaMap_self]
    simp only [LinearMap.id_apply, Pi.single_apply, hne.symm, ite_false, abs_zero]
    exact mul_nonneg (oldGammaConst_nonneg (by linarith)) (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  · have hdpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne (parabolicNorm_nonneg _) (Ne.symm hd)
    rw [translate_gammaMap_single]
    set g := (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C
      (y + a) (x + a) with hgdef
    have hshift (i : Fin 4) :
        |g.shift i| ≤ A * parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) := by
      have := canonicalGamma_shift_bound N κ noise (x + a) (y + a) i
      rw [add_sub_add_right_eq_sub] at this
      exact this.trans (le_mul_of_one_le_left (Real.rpow_nonneg (parabolicNorm_nonneg _) _) hA)
    have hp' : |g.cPsi| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
      rw [translate_gammaMap_single, structureBasisAction_iPsi_one] at hp
      exact hp
    have hpg' (i : Fin 3) : |g.cPsiGrad i| ≤
        A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
      have := hpg i
      rw [translate_gammaMap_single, structureBasisAction_iPsi_x] at this
      exact this
    have hs' : |g.cPsiSq| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiSq_one] at hs
      exact hs
    have hc' : |g.cPsiCube| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      rw [translate_gammaMap_single, structureBasisAction_iPsiCube_one] at hc
      exact hc
    exact gammaStructureBasis_weighted_bound κ g hdpos (by linarith) hshift hp' hpg' hs' hc' τ σ

end RegularityStructures.Phi43.Restart

end
