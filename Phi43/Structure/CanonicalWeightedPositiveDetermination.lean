/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalPositiveDetermination
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Weighted.Operator
import Mathlib.Tactic
public import RegularityStructures.Abstract.Model

/-!
# Weighted positive-degree determination for the Φ⁴₃ model

This is the polynomially weighted form of the positive-sector argument in Hairer
[Hai14, Proposition 3.31 and Theorem 8.44].  The compact model norm is local,
whereas the non-compact parabolic kernel requires a moderate polynomial weight.
The weighted Q-family uniqueness theorem is therefore applied to the difference
of two base-independent positive-degree Q-families.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem qFamily_eq_zero_of_weighted_diagonal_bound
    {D : parabolicSemigroup.distributions} {ρ : ParabolicSpace → ℝ} {p α C : ℝ}
    (hρ : parabolicSemigroup.IsModerateWeight ρ p) (hα : 0 < α)
    (hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
      |(D : ℝ → ParabolicSpace → ℝ) t x| ≤
        C * ρ x * t ^ (α / parabolicSemigroup.order)) : D = 0 := by
  apply Subtype.ext
  exact parabolicSemigroup.eq_of_abs_sub_le_weight hρ D.property
    parabolicSemigroup.distributions.zero_mem (div_pos hα parabolicSemigroup.order_pos) (by
      intro t ht x
      simpa using hbound t ht x)

private theorem canonical_gammaMap_eq_phi43
    {κ : Phi43.Kappa}
    {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {x y : ParabolicSpace} {g : Phi43.G}
    (hg : Phi43.phi43StructureGroupElement g = ↑(Z.gamma x y)) :
    Z.gammaMap x y =
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) := by
  simpa [Model.gammaMap] using congrArg
    (fun u : LinearMap.GeneralLinearGroup ℝ (Phi43.Symbol → ℝ) =>
      (u : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))) hg.symm

private noncomputable def canonical_phi43_rep
    {κ : Phi43.Kappa}
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (x y : ParabolicSpace) : Phi43.G :=
  Classical.choose (Z.gamma x y).2

private theorem canonical_phi43_rep_spec
    {κ : Phi43.Kappa}
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (x y : ParabolicSpace) :
    Phi43.phi43StructureGroupElement (canonical_phi43_rep Z x y) = ↑(Z.gamma x y) := by
  exact Classical.choose_spec (Z.gamma x y).2

private theorem canonicalModels_relevant_parameters
    (N : ℕ) (κ : Phi43.Kappa)
    (noise : Phi43.CanonicalNoise) (C : Phi43.RenormalisationConstants)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (x y : ParabolicSpace) :
    (∀ i : Fin 3,
      (canonical_phi43_rep Z x y).shift i.succ = (canonical_phi43_rep Z' x y).shift i.succ) ∧
      (canonical_phi43_rep Z x y).cPsi = (canonical_phi43_rep Z' x y).cPsi ∧
      (∀ i : Fin 3,
        (canonical_phi43_rep Z x y).cPsiGrad i = (canonical_phi43_rep Z' x y).cPsiGrad i) ∧
      (canonical_phi43_rep Z x y).cPsiSq = (canonical_phi43_rep Z' x y).cPsiSq ∧
      (canonical_phi43_rep Z x y).cPsiCube = (canonical_phi43_rep Z' x y).cPsiCube := by
  exact canonicalModels_relevant_parameters_eq_weighted N κ noise C Z Z' hZ hZ'
    x y (canonical_phi43_rep Z x y) (canonical_phi43_rep Z' x y)
      (canonical_phi43_rep_spec Z x y) (canonical_phi43_rep_spec Z' x y)

private theorem model_pi_eq_of_weighted_common_action
    (κ : Phi43.Kappa)
    (ρ : ParabolicSpace → ℝ) (p B B' : ℝ)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hρ : parabolicSemigroup.IsModerateWeight ρ p)
    (hPi : Z.PiBoundGrowth (gamma κ) B ρ)
    (hPi' : Z'.PiBoundGrowth (gamma κ) B' ρ)
    {τ : Phi43.Symbol} (hτ : homogeneity κ τ < gamma κ)
    (hpos : 0 < homogeneity κ τ)
    (hcommon : ∀ x y, ∃ l : Phi43.Symbol → ℝ,
      Z.gammaMap x y (Pi.single τ 1) = Pi.single τ 1 + l ∧
      Z'.gammaMap x y (Pi.single τ 1) = Pi.single τ 1 + l ∧
      Z.pi x l = Z'.pi x l) :
    ∀ x, Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) := by
  let e : Phi43.Symbol → ℝ := Pi.single τ 1
  let D : parabolicSemigroup.distributions :=
    Z.pi (0 : ParabolicSpace) e - Z'.pi (0 : ParabolicSpace) e
  have hconst : ∀ x y,
      Z.pi y e - Z'.pi y e = Z.pi x e - Z'.pi x e := by
    intro x y
    obtain ⟨l, hγ, hγ', hl⟩ := hcommon x y
    calc
      Z.pi y e - Z'.pi y e =
          Z.pi x (Z.gammaMap x y e) - Z'.pi x (Z'.gammaMap x y e) := by
        rw [Z.pi_gammaMap x y e, Z'.pi_gammaMap x y e]
      _ = Z.pi x (e + l) - Z'.pi x (e + l) := by rw [hγ, hγ']
      _ = Z.pi x e - Z'.pi x e := by
        rw [map_add, map_add, hl]
        abel
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
      |(D : ℝ → ParabolicSpace → ℝ) t x| ≤
        (B + B') * ρ x * t ^ (homogeneity κ τ / parabolicSemigroup.order) := by
    intro t ht x
    have hDx : D = Z.pi x e - Z'.pi x e := by
      exact (hconst (0 : ParabolicSpace) x).symm
    rw [hDx]
    change |Z.regPi x e t x - Z'.regPi x e t x| ≤ _
    calc
      |Z.regPi x e t x - Z'.regPi x e t x| ≤
          |Z.regPi x e t x| + |Z'.regPi x e t x| := by
            calc
              |Z.regPi x e t x - Z'.regPi x e t x| =
                  |Z.regPi x e t x + -Z'.regPi x e t x| := by rw [sub_eq_add_neg]
              _ ≤ |Z.regPi x e t x| + |-Z'.regPi x e t x| := abs_add_le _ _
              _ = |Z.regPi x e t x| + |Z'.regPi x e t x| := by rw [abs_neg]
      _ ≤ B * ρ x * t ^ (homogeneity κ τ / parabolicSemigroup.order) +
          B' * ρ x * t ^ (homogeneity κ τ / parabolicSemigroup.order) :=
        add_le_add (hPi τ hτ t ht x) (hPi' τ hτ t ht x)
      _ = (B + B') * ρ x * t ^ (homogeneity κ τ / parabolicSemigroup.order) := by ring
  have hD : D = 0 := qFamily_eq_zero_of_weighted_diagonal_bound hρ hpos hbound
  intro x
  apply sub_eq_zero.mp
  calc
    Z.pi x e - Z'.pi x e = Z.pi (0 : ParabolicSpace) e - Z'.pi (0 : ParabolicSpace) e :=
      hconst (0 : ParabolicSpace) x
    _ = D := rfl
    _ = 0 := hD

theorem canonicalModels_agree_below_gamma_of_weighted_growth
    (N : ℕ) (κ : Phi43.Kappa)
    (noise : Phi43.CanonicalNoise)
    (C : Phi43.RenormalisationConstants)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (ρ : ParabolicSpace → ℝ) (p : ℝ)
    (hρ : parabolicSemigroup.IsModerateWeight ρ p)
    (B B' : ℝ)
    (hPi : Z.PiBoundGrowth (Phi43.gamma κ) B ρ)
    (hPi' : Z'.PiBoundGrowth (Phi43.gamma κ) B' ρ)
    (hZ : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z') :
    ∀ (x : ParabolicSpace) (τ : Phi43.Symbol),
      homogeneity κ τ < gamma κ →
      Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) := by
  have hpoly (x : ParabolicSpace) {a : Phi43.Symbol → ℝ}
      (ha : a ∈ (Phi43.phi43PolynomialSector κ).subspace) :
      Z.pi x a = Z'.pi x a :=
    canonicalModels_pi_polynomial_subspace_eq_weighted N κ Z Z' hZ.1 hZ'.1 ha
  have hone (x : ParabolicSpace) :
      Z.pi x (Pi.single .one 1) = Z'.pi x (Pi.single .one 1) :=
    hpoly x (phi43Polynomial_one_mem κ)
  have hx (x : ParabolicSpace) (i : Fin 3) :
      Z.pi x (Pi.single (.x i) 1) = Z'.pi x (Pi.single (.x i) 1) :=
    hpoly x (phi43Polynomial_x_mem κ i)
  have hminus (τ : Phi43.Symbol) (hτ : τ ∈ Phi43.fMinus) (x : ParabolicSpace) :
      Z.pi x (Pi.single τ 1) = Z'.pi x (Pi.single τ 1) :=
    canonicalModels_pi_fMinus_eq N κ noise C Z Z' hZ hZ' τ hτ x
  have hIntegration_psi :
      Phi43.phi43AbstractIntegration (Pi.single .psi 1) = Pi.single .iPsi 1 := by
    ext σ
    rw [Phi43.phi43AbstractIntegration_apply_coord]
    cases σ <;> simp
  have hIntegration_psiSq :
      Phi43.phi43AbstractIntegration (Pi.single .psiSq 1) = Pi.single .iPsiSq 1 := by
    ext σ
    rw [Phi43.phi43AbstractIntegration_apply_coord]
    cases σ <;> simp
  have hIntegration_psiCube :
      Phi43.phi43AbstractIntegration (Pi.single .psiCube 1) = Pi.single .iPsiCube 1 := by
    ext σ
    rw [Phi43.phi43AbstractIntegration_apply_coord]
    cases σ <;> simp
  have hiPsi (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsi 1) = Z'.pi x (Pi.single .iPsi 1) := by
    have h := canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psi (by simp) x
    rw [hIntegration_psi] at h
    exact h
  have hiPsiSq (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiSq 1) = Z'.pi x (Pi.single .iPsiSq 1) := by
    have h := canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psiSq (by simp) x
    rw [hIntegration_psiSq] at h
    exact h
  have hiPsiCube (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiCube 1) = Z'.pi x (Pi.single .iPsiCube 1) := by
    have h := canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psiCube (by simp) x
    rw [hIntegration_psiCube] at h
    exact h
  have hpsiX (i : Fin 3) (x : ParabolicSpace) :
      Z.pi x (Pi.single (.psiX i) 1) = Z'.pi x (Pi.single (.psiX i) 1) := by
    apply model_pi_eq_of_weighted_common_action κ ρ p B B' Z Z' hρ hPi hPi'
      (τ := .psiX i)
      (by simp only [homogeneity, gamma]; linarith [kappa_pos κ, kappa_lt_kappa₀ κ])
      (by
        have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
        simp only [homogeneity]
        linarith)
    intro x y
    let g := canonical_phi43_rep Z x y
    let h := canonical_phi43_rep Z' x y
    have hg := canonical_phi43_rep_spec Z x y
    have hh := canonical_phi43_rep_spec Z' x y
    obtain ⟨hshift, hc, hgrad, hcSq, hcCube⟩ :=
      canonicalModels_relevant_parameters N κ noise C Z Z' hZ hZ' x y
    refine ⟨g.shift i.succ • Pi.single .psi 1, ?_, ?_, ?_⟩
    · calc
        Z.gammaMap x y (Pi.single (.psiX i) 1) =
            (Phi43.phi43StructureGroupElement g :
            (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single (.psiX i) 1) :=
          congrArg (fun L => L (Pi.single (.psiX i) 1)) (canonical_gammaMap_eq_phi43 hg)
        _ = Pi.single (.psiX i) 1 + g.shift i.succ • Pi.single .psi 1 :=
          phi43StructureGroupElement_single_psiX g i
    · calc
        Z'.gammaMap x y (Pi.single (.psiX i) 1) =
            (Phi43.phi43StructureGroupElement h :
            (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single (.psiX i) 1) :=
          congrArg (fun L => L (Pi.single (.psiX i) 1)) (canonical_gammaMap_eq_phi43 hh)
        _ = Pi.single (.psiX i) 1 + h.shift i.succ • Pi.single .psi 1 :=
          phi43StructureGroupElement_single_psiX h i
        _ = Pi.single (.psiX i) 1 + g.shift i.succ • Pi.single .psi 1 := by
          rw [hshift i]
    · calc
        Z.pi x (g.shift i.succ • Pi.single .psi 1) =
            g.shift i.succ • Z.pi x (Pi.single .psi 1) := by rw [map_smul]
        _ = g.shift i.succ • Z'.pi x (Pi.single .psi 1) :=
          congrArg (fun v : parabolicSemigroup.distributions => g.shift i.succ • v)
            (hminus .psi (by simp [Phi43.fMinus, Phi43.isFMinus]) x)
        _ = Z'.pi x (g.shift i.succ • Pi.single .psi 1) := by rw [map_smul]
  have hpsiSqX (i : Fin 3) (x : ParabolicSpace) :
      Z.pi x (Pi.single (.psiSqX i) 1) = Z'.pi x (Pi.single (.psiSqX i) 1) :=
    hminus (.psiSqX i) (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  have hiPsiPsi (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiPsi 1) = Z'.pi x (Pi.single .iPsiPsi 1) := by
    apply model_pi_eq_of_weighted_common_action κ ρ p B B' Z Z' hρ hPi hPi'
      (τ := .iPsiPsi)
      (by simp only [homogeneity, gamma]; linarith [kappa_pos κ])
      (by
        have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
        simp only [homogeneity]
        linarith)
    intro x y
    let g := canonical_phi43_rep Z x y
    let h := canonical_phi43_rep Z' x y
    have hg := canonical_phi43_rep_spec Z x y
    have hh := canonical_phi43_rep_spec Z' x y
    obtain ⟨hshift, hc, hgrad, hcSq, hcCube⟩ :=
      canonicalModels_relevant_parameters N κ noise C Z Z' hZ hZ' x y
    let l : Phi43.Symbol → ℝ :=
      g.cPsi • Pi.single .psi 1 + ∑ i, g.cPsiGrad i • Pi.single (.psiX i) 1
    refine ⟨l, ?_, ?_, ?_⟩
    · calc
        Z.gammaMap x y (Pi.single .iPsiPsi 1) =
            (Phi43.phi43StructureGroupElement g :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiPsi 1) :=
          congrArg (fun L => L (Pi.single .iPsiPsi 1)) (canonical_gammaMap_eq_phi43 hg)
        _ = Pi.single .iPsiPsi 1 + l := by
          rw [phi43StructureGroupElement_single_iPsiPsi]
          simp only [l]
          abel
    · calc
        Z'.gammaMap x y (Pi.single .iPsiPsi 1) =
            (Phi43.phi43StructureGroupElement h :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiPsi 1) :=
          congrArg (fun L => L (Pi.single .iPsiPsi 1)) (canonical_gammaMap_eq_phi43 hh)
        _ = Pi.single .iPsiPsi 1 +
            h.cPsi • Pi.single .psi 1 +
            ∑ i, h.cPsiGrad i • Pi.single (.psiX i) 1 := phi43StructureGroupElement_single_iPsiPsi h
        _ = Pi.single .iPsiPsi 1 + l := by
          simp only [l]
          have hsum :
              (∑ i, h.cPsiGrad i • Pi.single (Phi43.Symbol.psiX i) 1) =
                ∑ i, g.cPsiGrad i • Pi.single (Phi43.Symbol.psiX i) 1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hgrad i]
          rw [← hc, hsum]
          abel
    · calc
        Z.pi x l = g.cPsi • Z.pi x (Pi.single .psi 1) +
            ∑ i, g.cPsiGrad i • Z.pi x (Pi.single (.psiX i) 1) := by
          simp [l, map_add, map_smul, map_sum]
        _ = g.cPsi • Z'.pi x (Pi.single .psi 1) +
            ∑ i, g.cPsiGrad i • Z'.pi x (Pi.single (.psiX i) 1) := by
          rw [hminus .psi (by simp [Phi43.fMinus, Phi43.isFMinus]) x]
          simp_rw [hpsiX]
        _ = Z'.pi x l := by
          simp [l, map_add, map_smul, map_sum]
  have hiPsiPsiSq (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiPsiSq 1) = Z'.pi x (Pi.single .iPsiPsiSq 1) := by
    apply model_pi_eq_of_weighted_common_action κ ρ p B B' Z Z' hρ hPi hPi'
      (τ := .iPsiPsiSq)
      (by simp only [homogeneity, gamma]; linarith [kappa_pos κ])
      (by
        have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
        simp only [homogeneity]
        linarith)
    intro x y
    let g := canonical_phi43_rep Z x y
    let h := canonical_phi43_rep Z' x y
    have hg := canonical_phi43_rep_spec Z x y
    have hh := canonical_phi43_rep_spec Z' x y
    obtain ⟨hshift, hc, hgrad, hcSq, hcCube⟩ :=
      canonicalModels_relevant_parameters N κ noise C Z Z' hZ hZ' x y
    let l : Phi43.Symbol → ℝ :=
      g.cPsi • Pi.single .psiSq 1 +
        ∑ i, g.cPsiGrad i • Pi.single (.psiSqX i) 1
    refine ⟨l, ?_, ?_, ?_⟩
    · calc
        Z.gammaMap x y (Pi.single .iPsiPsiSq 1) =
            (Phi43.phi43StructureGroupElement g :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiPsiSq 1) :=
          congrArg (fun L => L (Pi.single .iPsiPsiSq 1)) (canonical_gammaMap_eq_phi43 hg)
        _ = Pi.single .iPsiPsiSq 1 + l := by
          rw [phi43StructureGroupElement_single_iPsiPsiSq]
          simp only [l]
          abel
    · calc
        Z'.gammaMap x y (Pi.single .iPsiPsiSq 1) =
            (Phi43.phi43StructureGroupElement h :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiPsiSq 1) :=
          congrArg (fun L => L (Pi.single .iPsiPsiSq 1)) (canonical_gammaMap_eq_phi43 hh)
        _ = Pi.single .iPsiPsiSq 1 +
            h.cPsi • Pi.single .psiSq 1 +
            ∑ i, h.cPsiGrad i • Pi.single (.psiSqX i) 1 :=
          phi43StructureGroupElement_single_iPsiPsiSq h
        _ = Pi.single .iPsiPsiSq 1 + l := by
          simp only [l]
          have hsum :
              (∑ i, h.cPsiGrad i • Pi.single (Phi43.Symbol.psiSqX i) 1) =
                ∑ i, g.cPsiGrad i • Pi.single (Phi43.Symbol.psiSqX i) 1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hgrad i]
          rw [← hc, hsum]
          abel
    · calc
        Z.pi x l = g.cPsi • Z.pi x (Pi.single .psiSq 1) +
            ∑ i, g.cPsiGrad i • Z.pi x (Pi.single (.psiSqX i) 1) := by
          simp [l, map_add, map_smul, map_sum]
        _ = g.cPsi • Z'.pi x (Pi.single .psiSq 1) +
            ∑ i, g.cPsiGrad i • Z'.pi x (Pi.single (.psiSqX i) 1) := by
          rw [hminus .psiSq (by simp [Phi43.fMinus, Phi43.isFMinus]) x]
          simp_rw [hpsiSqX]
        _ = Z'.pi x l := by
          simp [l, map_add, map_smul, map_sum]
  have hiPsiSqPsi (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiSqPsi 1) = Z'.pi x (Pi.single .iPsiSqPsi 1) := by
    apply model_pi_eq_of_weighted_common_action κ ρ p B B' Z Z' hρ hPi hPi'
      (τ := .iPsiSqPsi)
      (by simp only [homogeneity, gamma]; linarith [kappa_pos κ])
      (by
        have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
        simp only [homogeneity]
        linarith)
    intro x y
    let g := canonical_phi43_rep Z x y
    let h := canonical_phi43_rep Z' x y
    have hg := canonical_phi43_rep_spec Z x y
    have hh := canonical_phi43_rep_spec Z' x y
    obtain ⟨hshift, hc, hgrad, hcSq, hcCube⟩ :=
      canonicalModels_relevant_parameters N κ noise C Z Z' hZ hZ' x y
    let l : Phi43.Symbol → ℝ := g.cPsiSq • Pi.single .psi 1
    refine ⟨l, ?_, ?_, ?_⟩
    · calc
        Z.gammaMap x y (Pi.single .iPsiSqPsi 1) =
            (Phi43.phi43StructureGroupElement g :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiSqPsi 1) :=
          congrArg (fun L => L (Pi.single .iPsiSqPsi 1)) (canonical_gammaMap_eq_phi43 hg)
        _ = Pi.single .iPsiSqPsi 1 + l := by
          rw [phi43StructureGroupElement_single_iPsiSqPsi]
    · calc
        Z'.gammaMap x y (Pi.single .iPsiSqPsi 1) =
            (Phi43.phi43StructureGroupElement h :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiSqPsi 1) :=
          congrArg (fun L => L (Pi.single .iPsiSqPsi 1)) (canonical_gammaMap_eq_phi43 hh)
        _ = Pi.single .iPsiSqPsi 1 + h.cPsiSq • Pi.single .psi 1 :=
          phi43StructureGroupElement_single_iPsiSqPsi h
        _ = Pi.single .iPsiSqPsi 1 + l := by
          simp only [l]
          rw [← hcSq]
    · calc
        Z.pi x (g.cPsiSq • Pi.single .psi 1) =
            g.cPsiSq • Z.pi x (Pi.single .psi 1) := by rw [map_smul]
        _ = g.cPsiSq • Z'.pi x (Pi.single .psi 1) :=
          congrArg (fun v : parabolicSemigroup.distributions => g.cPsiSq • v)
            (hminus .psi (by simp [Phi43.fMinus, Phi43.isFMinus]) x)
        _ = Z'.pi x (g.cPsiSq • Pi.single .psi 1) := by rw [map_smul]
  have hiPsiCubeSq (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiCubeSq 1) = Z'.pi x (Pi.single .iPsiCubeSq 1) := by
    apply model_pi_eq_of_weighted_common_action κ ρ p B B' Z Z' hρ hPi hPi'
      (τ := .iPsiCubeSq)
      (by simp only [homogeneity, gamma]; linarith [kappa_pos κ])
      (by
        have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
        simp only [homogeneity]
        linarith)
    intro x y
    let g := canonical_phi43_rep Z x y
    let h := canonical_phi43_rep Z' x y
    have hg := canonical_phi43_rep_spec Z x y
    have hh := canonical_phi43_rep_spec Z' x y
    obtain ⟨hshift, hc, hgrad, hcSq, hcCube⟩ :=
      canonicalModels_relevant_parameters N κ noise C Z Z' hZ hZ' x y
    let l : Phi43.Symbol → ℝ :=
      (2 * g.cPsiCube) • Pi.single .iPsiCube 1 +
        (g.cPsiCube ^ 2) • Pi.single .one 1
    refine ⟨l, ?_, ?_, ?_⟩
    · calc
        Z.gammaMap x y (Pi.single .iPsiCubeSq 1) =
            (Phi43.phi43StructureGroupElement g :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiCubeSq 1) :=
          congrArg (fun L => L (Pi.single .iPsiCubeSq 1)) (canonical_gammaMap_eq_phi43 hg)
        _ = Pi.single .iPsiCubeSq 1 + l := by
          rw [phi43StructureGroupElement_single_iPsiCubeSq]
          simp only [l]
          abel
    · calc
        Z'.gammaMap x y (Pi.single .iPsiCubeSq 1) =
            (Phi43.phi43StructureGroupElement h :
              (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
              (Pi.single .iPsiCubeSq 1) :=
          congrArg (fun L => L (Pi.single .iPsiCubeSq 1)) (canonical_gammaMap_eq_phi43 hh)
        _ = Pi.single .iPsiCubeSq 1 +
            (2 * h.cPsiCube) • Pi.single .iPsiCube 1 +
            (h.cPsiCube ^ 2) • Pi.single .one 1 :=
          phi43StructureGroupElement_single_iPsiCubeSq h
        _ = Pi.single .iPsiCubeSq 1 + l := by
          simp only [l]
          rw [← hcCube]
          abel
    · calc
        Z.pi x l = (2 * g.cPsiCube) • Z.pi x (Pi.single .iPsiCube 1) +
            (g.cPsiCube ^ 2) • Z.pi x (Pi.single .one 1) := by
          simp [l, map_add, map_smul]
        _ = (2 * g.cPsiCube) • Z'.pi x (Pi.single .iPsiCube 1) +
            (g.cPsiCube ^ 2) • Z'.pi x (Pi.single .one 1) := by
          rw [hiPsiCube x, hone x]
        _ = Z'.pi x l := by
          simp [l, map_add, map_smul]
  intro x τ hτ
  cases τ with
  | one => exact hone x
  | noise => exact hminus .noise (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | x0 =>
      simp only [homogeneity, gamma] at hτ
      exfalso
      have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
      linarith
  | x i => exact hx x i
  | xMul q =>
      simp only [homogeneity, gamma] at hτ
      exfalso
      have hk : κ.1 < (1 : ℝ) / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
      linarith
  | psi => exact hminus .psi (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | iPsi =>
      simp only [homogeneity, gamma] at hτ
      exfalso
      exact (not_lt_of_ge (le_of_lt (gamma_lt_iPsi κ))) hτ
  | psiSq => exact hminus .psiSq (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | psiCube => exact hminus .psiCube (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | psiX i => exact hpsiX i x
  | psiSqX i => exact hpsiSqX i x
  | iPsiSq => exact hiPsiSq x
  | iPsiCube => exact hiPsiCube x
  | iPsiPsi => exact hiPsiPsi x
  | iPsiPsiSq => exact hiPsiPsiSq x
  | iPsiSqPsi => exact hiPsiSqPsi x
  | iPsiSqPsiSq => exact hminus .iPsiSqPsiSq (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | iPsiCubePsi => exact hminus .iPsiCubePsi (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | iPsiCubePsiSq => exact hminus .iPsiCubePsiSq (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  | iPsiCubeSq => exact hiPsiCubeSq x

end RegularityStructures.Phi43

end
