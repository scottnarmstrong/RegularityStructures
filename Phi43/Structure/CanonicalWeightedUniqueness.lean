/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalWeightedPositiveDetermination
public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import RegularityStructures.Probability.ModelKolmogorovNorm
import Mathlib.Tactic

/-!
# Weighted uniqueness of the renormalised canonical model

The predicate `Statements.IsModerateRenormalisedCanonicalModel` supplies a
moderate polynomial weight for each model.  The product
of two such weights is again moderate and dominates both original weights, so
the weighted positive-sector theorem determines the two `Π` maps below the
fixed-point cutoff.  The concrete finite structure group then determines the
corresponding `Γ` maps on the inputs inspected by `gammaDiffNormOn`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem isRenormalisedCanonicalModel_of_moderate
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)
    {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) :
    Statements.IsRenormalisedCanonicalModel N κ noise C Z := by
  unfold Statements.IsModerateRenormalisedCanonicalModel at hZ
  exact ⟨hZ.1, hZ.2.1, hZ.2.2.1⟩

private theorem moderateWeight_mul
    {ρ ρ' : ParabolicSpace → ℝ} {p p' : ℝ}
    (hρ : parabolicSemigroup.IsModerateWeight ρ p)
    (hρ' : parabolicSemigroup.IsModerateWeight ρ' p') :
    parabolicSemigroup.IsModerateWeight (fun z => ρ z * ρ' z) (p + p') where
  one_le x := one_le_mul_of_one_le_of_one_le (hρ.one_le x) (hρ'.one_le x)
  measurable := hρ.measurable.mul hρ'.measurable
  nonneg_exp := add_nonneg hρ.nonneg_exp hρ'.nonneg_exp
  le y z := by
    have hd : 0 < 1 + parabolicSemigroup.scaleDist z y := by
      linarith [parabolicSemigroup.scaleDist_nonneg z y]
    calc
      ρ z * ρ' z ≤
          (ρ y * (1 + parabolicSemigroup.scaleDist z y) ^ p) *
            (ρ' y * (1 + parabolicSemigroup.scaleDist z y) ^ p') :=
        mul_le_mul (hρ.le y z) (hρ'.le y z)
          (zero_le_one.trans (hρ'.one_le z))
          (mul_nonneg (zero_le_one.trans (hρ.one_le y)) (Real.rpow_nonneg hd.le _))
      _ = ρ y * ρ' y *
          (1 + parabolicSemigroup.scaleDist z y) ^ (p + p') := by
        rw [Real.rpow_add hd]
        ring

private theorem piBoundGrowth_mono
    {κ : Kappa} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {B : ℝ} {ρ σ : ParabolicSpace → ℝ} (hB : 0 ≤ B)
    (hρσ : ∀ x, ρ x ≤ σ x)
    (h : Z.PiBoundGrowth (gamma κ) B ρ) :
    Z.PiBoundGrowth (gamma κ) B σ := by
  intro i hi t ht x
  exact (h i hi t ht x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hρσ x) hB) (Real.rpow_nonneg ht.1.le _))

private theorem moderate_pi_eq
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z') :
    ∀ (x : ParabolicSpace) (τ : Symbol),
      homogeneity κ τ < gamma κ →
      Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) := by
  obtain ⟨h1, h2, h3, ρ, p, B, hρ, hB, hPi⟩ := hZ
  obtain ⟨h1', h2', h3', ρ', p', B', hρ', hB', hPi'⟩ := hZ'
  exact canonicalModels_agree_below_gamma_of_weighted_growth
    N κ noise C Z Z' (fun z => ρ z * ρ' z) (p + p')
    (moderateWeight_mul hρ hρ') B B'
    (piBoundGrowth_mono hB (fun x => le_mul_of_one_le_right
      (zero_le_one.trans (hρ.one_le x)) (hρ'.one_le x)) hPi)
    (piBoundGrowth_mono hB' (fun x => le_mul_of_one_le_left
      (zero_le_one.trans (hρ'.one_le x)) (hρ.one_le x)) hPi')
    ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩

private theorem structureGroupMap_basis_eq_of_relevant_params
    (κ : Kappa) {g h : G}
    (hshift : ∀ i : Fin 3, g.shift i.succ = h.shift i.succ)
    (hc : g.cPsi = h.cPsi)
    (hgrad : ∀ i : Fin 3, g.cPsiGrad i = h.cPsiGrad i)
    (hSq : g.cPsiSq = h.cPsiSq)
    (hCube : g.cPsiCube = h.cPsiCube)
    {τ : Symbol} (hτ : homogeneity κ τ < gamma κ) :
    structureGroupMap g (basis τ) = structureGroupMap h (basis τ) := by
  have hk : κ.1 < (1 : ℝ) / 16 := by
    simpa [kappa₀] using kappa_lt_kappa₀ κ
  cases τ with
  | one => simp [structureGroupMap_basis, structureBasisAction, primitiveAction]
  | noise => simp [structureGroupMap_basis, structureBasisAction, primitiveAction]
  | x0 =>
      simp only [homogeneity, gamma] at hτ
      exfalso
      linarith
  | x i =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction, hshift i]
  | xMul p =>
      simp only [homogeneity, gamma] at hτ
      exfalso
      linarith
  | psi => simp [structureGroupMap_basis, structureBasisAction, primitiveAction]
  | iPsi =>
      exfalso
      exact (not_lt_of_ge (le_of_lt (gamma_lt_iPsi κ))) hτ
  | psiSq =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol]
  | psiCube =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol]
  | psiX i =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hshift i]
  | psiSqX i =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hshift i]
  | iPsiSq =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction, hSq]
  | iPsiCube =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction, hCube]
  | iPsiPsi =>
      simp [structureGroupMap_basis, structureBasisAction, integratedPsiProductAction,
        hgrad, hc]
  | iPsiPsiSq =>
      simp [structureGroupMap_basis, structureBasisAction, integratedPsiProductAction,
        hgrad, hc]
  | iPsiSqPsi =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hSq]
  | iPsiSqPsiSq =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hSq]
  | iPsiCubePsi =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hCube]
  | iPsiCubePsiSq =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hCube]
  | iPsiCubeSq =>
      simp [structureGroupMap_basis, structureBasisAction, primitiveAction,
        multiply_basis, basisProduct, productSymbol, hCube]

private theorem phi43StructureGroupElement_apply_single_eq_of_relevant_params
    (κ : Kappa) {g h : G}
    (hshift : ∀ i : Fin 3, g.shift i.succ = h.shift i.succ)
    (hc : g.cPsi = h.cPsi)
    (hgrad : ∀ i : Fin 3, g.cPsiGrad i = h.cPsiGrad i)
    (hSq : g.cPsiSq = h.cPsiSq)
    (hCube : g.cPsiCube = h.cPsiCube)
    {τ : Symbol} (hτ : homogeneity κ τ < gamma κ) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single τ 1) =
      (phi43StructureGroupElement h : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single τ 1) := by
  rw [phi43StructureGroupElement_apply_single, phi43StructureGroupElement_apply_single]
  exact congrArg phi43CoordinateEquiv
    (structureGroupMap_basis_eq_of_relevant_params κ hshift hc hgrad hSq hCube hτ)

private theorem gammaMap_eq_phi43
    {κ : Kappa} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {x y : ParabolicSpace} {g : G}
    (hg : phi43StructureGroupElement g = ↑(Z.gamma x y)) :
    Z.gammaMap x y =
      (phi43StructureGroupElement g :
        (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) := by
  simpa [Model.gammaMap] using congrArg
    (fun u : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ) =>
      (u : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))) hg.symm

private theorem moderate_gamma_map_single_eq
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z')
    (x y : ParabolicSpace) (τ : Symbol)
    (hτ : homogeneity κ τ < gamma κ) :
    Z.gammaMap x y (Pi.single τ 1) = Z'.gammaMap x y (Pi.single τ 1) := by
  let g := Classical.choose (Z.gamma x y).2
  let h := Classical.choose (Z'.gamma x y).2
  have hg : phi43StructureGroupElement g = ↑(Z.gamma x y) :=
    Classical.choose_spec (Z.gamma x y).2
  have hh : phi43StructureGroupElement h = ↑(Z'.gamma x y) :=
    Classical.choose_spec (Z'.gamma x y).2
  obtain ⟨hshift, hc, hgrad, hSq, hCube⟩ :=
    canonicalModels_relevant_parameters_eq_weighted
      N κ noise C Z Z' (isRenormalisedCanonicalModel_of_moderate N κ noise C hZ) (isRenormalisedCanonicalModel_of_moderate N κ noise C hZ')
      x y g h hg hh
  calc
    Z.gammaMap x y (Pi.single τ 1) =
        (phi43StructureGroupElement g :
          (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single τ 1) := by
      exact congrArg (fun L => L (Pi.single τ 1)) (gammaMap_eq_phi43 hg)
    _ = (phi43StructureGroupElement h :
          (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single τ 1) :=
      phi43StructureGroupElement_apply_single_eq_of_relevant_params
        κ hshift hc hgrad hSq hCube hτ
    _ = Z'.gammaMap x y (Pi.single τ 1) := by
      exact congrArg (fun L => L (Pi.single τ 1)) (gammaMap_eq_phi43 hh).symm

theorem renormalisedCanonicalModel_piDiffNormOn_eq_zero
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z') :
    Z.piDiffNormOn Z' (gamma κ) Set.univ = 0 := by
  have h := moderate_pi_eq N κ noise C Z Z' hZ hZ'
  refine le_antisymm ((iInf₂_le 0 ?_).trans (by simp)) bot_le
  intro τ hτ t _ x _
  simp [Model.regPi, h x τ hτ]

theorem renormalisedCanonicalModel_gammaDiffNormOn_eq_zero
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z') :
    Z.gammaDiffNormOn Z' (gamma κ) Set.univ = 0 := by
  refine le_antisymm ((iInf₂_le 0 ?_).trans (by simp)) bot_le
  intro i j hi hj x _ y _
  have hxy := moderate_gamma_map_single_eq N κ noise C Z Z' hZ hZ' y x i hi
  have hcoord := congrFun hxy j
  simp [hcoord]

end RegularityStructures.Phi43

end
