/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalCoreUniqueness
public import Phi43.Structure.Abstract
public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Abstract.Integration.PolyCompat.Compat
public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
public import RegularityStructures.Abstract.Model

/-!
# Positive-degree determination for the canonical-model predicate

This module supplies the compact-norm step needed after the negative and integrated
sectors have been identified.  A positive-order `Q`-family with the model diagonal
bound is zero: iterate the semigroup identity and let the input scale tend to zero.
The Φ⁴₃ application is recorded below in a separate theorem.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

private theorem phi43AbstractIntegration_source_single (τ : Phi43.Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    Phi43.phi43AbstractIntegration (Pi.single τ 1) =
      Pi.single (match τ with
        | .noise => .psi
        | .psi => .iPsi
        | .psiSq => .iPsiSq
        | .psiCube => .iPsiCube
        | _ => .one) 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;>
    ext σ <;> cases σ <;> simp [Phi43.phi43AbstractIntegration_apply_coord]

private theorem model_pi_eq_on_polynomial_subspace
    (N : ℕ) (κ : Phi43.Kappa)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Z.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    (hZ' : Z'.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    {x : ParabolicSpace} {a : Phi43.Symbol → ℝ}
    (ha : a ∈ (Phi43.phi43PolynomialSector κ).subspace) : Z.pi x a = Z'.pi x a := by
  have hpolyZ : Z.IsPolyCompatible (Phi43.phi43PolynomialSector κ) :=
    hZ.poly
  have hpolyZ' : Z'.IsPolyCompatible (Phi43.phi43PolynomialSector κ) :=
    hZ'.poly
  have hterm : ∀ k, Z.pi x (Pi.single ((Phi43.phi43PolynomialSector κ).emb k) 1) =
      Z'.pi x (Pi.single ((Phi43.phi43PolynomialSector κ).emb k) 1) := by
    intro k
    apply Subtype.ext
    funext t z
    exact (hpolyZ x k t z).trans (hpolyZ' x k t z).symm
  change Z.pi x a = Z'.pi x a
  rw [PolynomialSector.eq_polyEmbed_of_mem (Phi43.phi43PolynomialSector κ) ha]
  simp only [PolynomialSector.polyEmbed, map_sum, map_smul]
  simp_rw [hterm]

private theorem phi43Group_iPsi (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsi 1) =
      (Pi.single .iPsi 1 : Phi43.Symbol → ℝ) + g.cPsi • (Pi.single .one 1 : Phi43.Symbol → ℝ) +
        ∑ i, g.cPsiGrad i • (Pi.single (.x i) 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply, Pi.single_apply]

private theorem phi43Group_x (g : Phi43.G) (i : Fin 3) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single (.x i) 1) =
      (Pi.single (.x i) 1 : Phi43.Symbol → ℝ) +
        g.shift i.succ • (Pi.single .one 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply]

private theorem phi43Group_iPsiSq (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiSq 1) =
      (Pi.single .iPsiSq 1 : Phi43.Symbol → ℝ) +
        g.cPsiSq • (Pi.single .one 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply]

private theorem phi43Group_iPsiCube (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiCube 1) =
      (Pi.single .iPsiCube 1 : Phi43.Symbol → ℝ) +
        g.cPsiCube • (Pi.single .one 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply]

private theorem phi43Group_psiX (g : Phi43.G) (i : Fin 3) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single (.psiX i) 1) =
      (Pi.single (.psiX i) 1 : Phi43.Symbol → ℝ) +
        g.shift i.succ • (Pi.single .psi 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis,
    Phi43.basisProduct, Phi43.productSymbol]
  ext σ; cases σ <;> simp [Pi.smul_apply]

private theorem phi43Group_iPsiPsi (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiPsi 1) =
      (Pi.single .iPsiPsi 1 : Phi43.Symbol → ℝ) + g.cPsi • (Pi.single .psi 1 : Phi43.Symbol → ℝ) +
        ∑ i, g.cPsiGrad i • (Pi.single (.psiX i) 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.integratedPsiProductAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply, Pi.single_apply]

private theorem phi43Group_iPsiPsiSq (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiPsiSq 1) =
      (Pi.single .iPsiPsiSq 1 : Phi43.Symbol → ℝ) +
        g.cPsi • (Pi.single .psiSq 1 : Phi43.Symbol → ℝ) +
        ∑ i, g.cPsiGrad i • (Pi.single (.psiSqX i) 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.integratedPsiProductAction, Phi43.basis]
  ext σ; cases σ <;> simp [Pi.smul_apply, Pi.single_apply]

private theorem phi43Group_iPsiSqPsi (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiSqPsi 1) =
      (Pi.single .iPsiSqPsi 1 : Phi43.Symbol → ℝ) +
        g.cPsiSq • (Pi.single .psi 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis,
    Phi43.basisProduct, Phi43.productSymbol]
  ext σ; cases σ <;> simp [Pi.smul_apply]

private theorem phi43Group_iPsiCubeSq (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiCubeSq 1) =
      (Pi.single .iPsiCubeSq 1 : Phi43.Symbol → ℝ) +
        (2 * g.cPsiCube) • (Pi.single .iPsiCube 1 : Phi43.Symbol → ℝ) +
        (g.cPsiCube ^ 2) • (Pi.single .one 1 : Phi43.Symbol → ℝ) := by
  rw [Phi43.phi43StructureGroupElement_apply_single]
  simp [Phi43.phi43CoordinateEquiv,
    Phi43.structureBasisAction, Phi43.primitiveAction, Phi43.basis,
    Phi43.basisProduct, Phi43.productSymbol]
  ext σ; cases σ <;> simp [Pi.smul_apply] <;> ring

private theorem phi43RelevantParameters_eq_of_actions {g h : Phi43.G}
    (hsi : ∀ i : Fin 3,
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
          (Pi.single (.x i) 1) =
        (Phi43.phi43StructureGroupElement h :
          (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single (.x i) 1))
    (hcp : (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsi 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1))
    (hcg : ∀ i : Fin 3,
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
          (Pi.single .iPsi 1) (.x i) =
        (Phi43.phi43StructureGroupElement h :
          (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1) (.x i))
    (hcs : (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiSq 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiSq 1))
    (hcc : (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))
        (Pi.single .iPsiCube 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiCube 1)) :
    (∀ i : Fin 3, g.shift i.succ = h.shift i.succ) ∧
      g.cPsi = h.cPsi ∧ (∀ i : Fin 3, g.cPsiGrad i = h.cPsiGrad i) ∧
        g.cPsiSq = h.cPsiSq ∧ g.cPsiCube = h.cPsiCube := by
  have hsi' (i : Fin 3) : g.shift i.succ = h.shift i.succ := by
    simpa [phi43Group_x, Pi.add_apply, Pi.single_eq_same, one_smul,
      Pi.smul_apply, smul_eq_mul] using congrFun (hsi i) .one
  have hcp' : g.cPsi = h.cPsi := by
    simpa [phi43Group_iPsi, Pi.add_apply, Pi.single_eq_same, one_smul,
      Pi.smul_apply, smul_eq_mul] using congrFun hcp .one
  have hcg' : ∀ i, g.cPsiGrad i = h.cPsiGrad i := by
    intro i
    have hi := hcg i
    fin_cases i <;>
      simpa [phi43Group_iPsi, Pi.add_apply, Pi.single_eq_same, one_smul,
        Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ] using hi
  have hcs' : g.cPsiSq = h.cPsiSq := by
    simpa [phi43Group_iPsiSq, Pi.add_apply, Pi.single_eq_same, one_smul,
      Pi.smul_apply, smul_eq_mul] using congrFun hcs .one
  have hcc' : g.cPsiCube = h.cPsiCube := by
    simpa [phi43Group_iPsiCube, Pi.add_apply, Pi.single_eq_same, one_smul,
      Pi.smul_apply, smul_eq_mul] using congrFun hcc .one
  exact ⟨hsi', hcp', hcg', hcs', hcc'⟩

private theorem phi43_poly_one_mem (κ : Phi43.Kappa) :
    (Pi.single .one 1 : Phi43.Symbol → ℝ) ∈
      (Phi43.phi43PolynomialSector κ).subspace := by
  intro τ hτ
  simp only [Pi.single_apply]
  split_ifs with h
  · subst τ
    let k : PolyIndex 2 := ⟨0, by simp [weight_parabolicWeight]⟩
    have hk : (Phi43.phi43PolynomialSector κ).emb k = .one := by
      simp [Phi43.phi43PolynomialSector, Phi43.phi43PolyEmb, k]
    exact False.elim (hτ ⟨k, hk⟩)
  · rfl

private theorem phi43_poly_x_mem (κ : Phi43.Kappa) (i : Fin 3) :
    (Pi.single (.x i) 1 : Phi43.Symbol → ℝ) ∈
      (Phi43.phi43PolynomialSector κ).subspace := by
  intro τ hτ
  simp only [Pi.single_apply]
  split_ifs with h
  · subst τ
    fin_cases i
    · let k : PolyIndex 2 :=
        ⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
      have hk : (Phi43.phi43PolynomialSector κ).emb k = .x 0 := by
        simp [Phi43.phi43PolynomialSector, Phi43.phi43PolyEmb, k]
      exact False.elim (hτ ⟨k, hk⟩)
    · let k : PolyIndex 2 :=
        ⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
      have hk : (Phi43.phi43PolynomialSector κ).emb k = .x 1 := by
        simp [Phi43.phi43PolynomialSector, Phi43.phi43PolyEmb, k]
      exact False.elim (hτ ⟨k, hk⟩)
    · let k : PolyIndex 2 :=
        ⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
      have hk : (Phi43.phi43PolynomialSector κ).emb k = .x 2 := by
        simp [Phi43.phi43PolynomialSector, Phi43.phi43PolyEmb, k]
      exact False.elim (hτ ⟨k, hk⟩)
  · rfl

private theorem model_poly_pi_injective_pair
    (N : ℕ) (κ : Phi43.Kappa)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Z.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    (hZ' : Z'.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    {x : ParabolicSpace} {a b : Phi43.Symbol → ℝ}
    (ha : a ∈ (Phi43.phi43PolynomialSector κ).subspace)
    (hb : b ∈ (Phi43.phi43PolynomialSector κ).subspace)
    (hpi : Z.pi x a = Z'.pi x b) : a = b := by
  have hpi' : Z.pi x a = Z.pi x b := by
    exact hpi.trans (model_pi_eq_on_polynomial_subspace N κ Z Z' hZ hZ' hb).symm
  apply sub_eq_zero.mp
  apply Model.eq_zero_of_regPi_eq_zero hZ.poly x (Submodule.sub_mem _ ha hb)
  intro t ht z
  have h := congrArg (fun v : parabolicSemigroup.distributions => (v : ℝ → ParabolicSpace → ℝ) t z)
    hpi'
  rw [Model.regPi_sub]
  exact sub_eq_zero.mpr h

private theorem canonicalModels_relevant_parameters_eq (N : ℕ) (κ : Phi43.Kappa)
    (noise : Phi43.CanonicalNoise) (C : Phi43.RenormalisationConstants)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (x y : ParabolicSpace) (g h : Phi43.G)
    (hg : Phi43.phi43StructureGroupElement g = ↑(Z.gamma x y))
    (hh : Phi43.phi43StructureGroupElement h = ↑(Z'.gamma x y)) :
    (∀ i : Fin 3, g.shift i.succ = h.shift i.succ) ∧
      g.cPsi = h.cPsi ∧ (∀ i : Fin 3, g.cPsiGrad i = h.cPsiGrad i) ∧
        g.cPsiSq = h.cPsiSq ∧ g.cPsiCube = h.cPsiCube := by
  have hone (x : ParabolicSpace) :
      Z.pi x (Pi.single .one 1) = Z'.pi x (Pi.single .one 1) :=
    model_pi_eq_on_polynomial_subspace N κ Z Z' hZ.1 hZ'.1
      (x := x) (phi43_poly_one_mem κ)
  have hx (x : ParabolicSpace) (i : Fin 3) :
      Z.pi x (Pi.single (.x i) 1) = Z'.pi x (Pi.single (.x i) 1) :=
    model_pi_eq_on_polynomial_subspace N κ Z Z' hZ.1 hZ'.1
      (x := x) (phi43_poly_x_mem κ i)
  have hpsi (x : ParabolicSpace) :
      Z.pi x (Pi.single .psi 1) = Z'.pi x (Pi.single .psi 1) := by
    exact Phi43.canonicalModels_pi_fMinus_eq N κ noise C Z Z' hZ hZ' .psi
      (by simp [Phi43.fMinus, Phi43.isFMinus]) x
  have hiPsi (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsi 1) = Z'.pi x (Pi.single .iPsi 1) := by
    have h := Phi43.canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psi (by simp) x
    rw [phi43AbstractIntegration_source_single .psi (by simp)] at h
    exact h
  have hiPsiSq (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiSq 1) = Z'.pi x (Pi.single .iPsiSq 1) := by
    have h := Phi43.canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psiSq (by simp) x
    rw [phi43AbstractIntegration_source_single .psiSq (by simp)] at h
    exact h
  have hiPsiCube (x : ParabolicSpace) :
      Z.pi x (Pi.single .iPsiCube 1) = Z'.pi x (Pi.single .iPsiCube 1) := by
    have h := Phi43.canonicalModels_pi_integrated_source_eq N κ noise C Z Z' hZ hZ'
      .psiCube (by simp) x
    rw [phi43AbstractIntegration_source_single .psiCube (by simp)] at h
    exact h
  have hγ : Z.gammaMap x y =
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) := by
    simpa [Model.gammaMap] using congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Phi43.Symbol → ℝ) =>
        (u : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))) hg.symm
  have hγ' : Z'.gammaMap x y =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) := by
    simpa [Model.gammaMap] using congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Phi43.Symbol → ℝ) =>
        (u : (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ))) hh.symm
  have haction_poly (e : Phi43.Symbol → ℝ)
      (he : e ∈ (Phi43.phi43PolynomialSector κ).subspace) :
      Z.gammaMap x y e = Z'.gammaMap x y e := by
    have hge : Z.gammaMap x y e ∈ (Phi43.phi43PolynomialSector κ).subspace :=
      (Phi43.phi43PolynomialSector κ).invariant (Z.gamma x y).1 (Z.gamma x y).2 e he
    have hge' : Z'.gammaMap x y e ∈ (Phi43.phi43PolynomialSector κ).subspace :=
      (Phi43.phi43PolynomialSector κ).invariant (Z'.gamma x y).1 (Z'.gamma x y).2 e he
    have hpi : Z.pi x (Z.gammaMap x y e) =
        Z'.pi x (Z'.gammaMap x y e) := by
      calc
        Z.pi x (Z.gammaMap x y e) = Z.pi y e := Z.pi_gamma x y e
        _ = Z'.pi y e := model_pi_eq_on_polynomial_subspace N κ Z Z' hZ.1 hZ'.1 he
        _ = Z'.pi x (Z'.gammaMap x y e) := (Z'.pi_gamma x y e).symm
    exact model_poly_pi_injective_pair N κ Z Z' hZ.1 hZ'.1 hge hge' hpi
  have hact_x (i : Fin 3) := haction_poly (Pi.single (.x i) 1) (phi43_poly_x_mem κ i)
  have hcor_iPsi_g :
      g.cPsi • Pi.single .one 1 +
          ∑ i, g.cPsiGrad i • Pi.single (.x i) 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
    · exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (phi43_poly_x_mem κ i)
  have hcor_iPsi_h :
      h.cPsi • Pi.single .one 1 +
          ∑ i, h.cPsiGrad i • Pi.single (.x i) 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
    · exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (phi43_poly_x_mem κ i)
  have hpi_iPsi :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsi 1)) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsi 1)) := by
    calc
      Z.pi x (Z.gammaMap x y (Pi.single .iPsi 1)) =
          Z.pi y (Pi.single .iPsi 1) := Z.pi_gamma x y _
      _ = Z'.pi y (Pi.single .iPsi 1) := hiPsi y
      _ = Z'.pi x (Z'.gammaMap x y (Pi.single .iPsi 1)) :=
        (Z'.pi_gamma x y _).symm
  have hmem_iPsi_g :
      Z.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ, phi43Group_iPsi]
    have heq :
        (Pi.single (Phi43.Symbol.iPsi) 1 + g.cPsi •
            Pi.single (Phi43.Symbol.one) 1 +
          ∑ i, g.cPsiGrad i • Pi.single (Phi43.Symbol.x i) 1) -
            Pi.single (Phi43.Symbol.iPsi) 1 =
          g.cPsi • Pi.single (Phi43.Symbol.one) 1 +
            ∑ i, g.cPsiGrad i • Pi.single (Phi43.Symbol.x i) 1 := by
      abel
    rw [heq]
    exact hcor_iPsi_g
  have hmem_iPsi_h :
      Z'.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ', phi43Group_iPsi]
    have heq :
        (Pi.single (Phi43.Symbol.iPsi) 1 + h.cPsi •
            Pi.single (Phi43.Symbol.one) 1 +
          ∑ i, h.cPsiGrad i • Pi.single (Phi43.Symbol.x i) 1) -
            Pi.single (Phi43.Symbol.iPsi) 1 =
          h.cPsi • Pi.single (Phi43.Symbol.one) 1 +
            ∑ i, h.cPsiGrad i • Pi.single (Phi43.Symbol.x i) 1 := by
      abel
    rw [heq]
    exact hcor_iPsi_h
  have hcor_iPsi_pi :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1) := by
    simp only [map_sub]
    exact congrArg₂ (fun u v : parabolicSemigroup.distributions => u - v)
      hpi_iPsi (hiPsi x)
  have hact_iPsi :
      Z.gammaMap x y (Pi.single .iPsi 1) =
        Z'.gammaMap x y (Pi.single .iPsi 1) := by
    have h := model_poly_pi_injective_pair N κ Z Z' hZ.1 hZ'.1
      hmem_iPsi_g hmem_iPsi_h hcor_iPsi_pi
    calc
      Z.gammaMap x y (Pi.single .iPsi 1) =
          (Z.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1) +
            Pi.single .iPsi 1 := by abel
      _ = (Z'.gammaMap x y (Pi.single .iPsi 1) - Pi.single .iPsi 1) +
            Pi.single .iPsi 1 := congrArg (fun v => v + Pi.single .iPsi 1) h
      _ = Z'.gammaMap x y (Pi.single .iPsi 1) := by abel
  have hpi_iPsiSq :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiSq 1)) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiSq 1)) := by
    calc
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiSq 1)) =
          Z.pi y (Pi.single .iPsiSq 1) := Z.pi_gamma x y _
      _ = Z'.pi y (Pi.single .iPsiSq 1) := hiPsiSq y
      _ = Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiSq 1)) :=
        (Z'.pi_gamma x y _).symm
  have hmem_iPsiSq_g :
      Z.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ, phi43Group_iPsiSq, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
  have hmem_iPsiSq_h :
      Z'.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ', phi43Group_iPsiSq, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
  have hcor_iPsiSq_pi :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1) := by
    simp only [map_sub]
    exact congrArg₂ (fun u v : parabolicSemigroup.distributions => u - v)
      hpi_iPsiSq (hiPsiSq x)
  have hact_iPsiSq :
      Z.gammaMap x y (Pi.single .iPsiSq 1) =
        Z'.gammaMap x y (Pi.single .iPsiSq 1) := by
    have h := model_poly_pi_injective_pair N κ Z Z' hZ.1 hZ'.1
      hmem_iPsiSq_g hmem_iPsiSq_h hcor_iPsiSq_pi
    calc
      Z.gammaMap x y (Pi.single .iPsiSq 1) =
          (Z.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1) +
            Pi.single .iPsiSq 1 := by abel
      _ = (Z'.gammaMap x y (Pi.single .iPsiSq 1) - Pi.single .iPsiSq 1) +
            Pi.single .iPsiSq 1 := congrArg (fun v => v + Pi.single .iPsiSq 1) h
      _ = Z'.gammaMap x y (Pi.single .iPsiSq 1) := by abel
  have hpi_iPsiCube :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiCube 1)) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiCube 1)) := by
    calc
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiCube 1)) =
          Z.pi y (Pi.single .iPsiCube 1) := Z.pi_gamma x y _
      _ = Z'.pi y (Pi.single .iPsiCube 1) := hiPsiCube y
      _ = Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiCube 1)) :=
        (Z'.pi_gamma x y _).symm
  have hmem_iPsiCube_g :
      Z.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ, phi43Group_iPsiCube, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
  have hmem_iPsiCube_h :
      Z'.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1 ∈
        (Phi43.phi43PolynomialSector κ).subspace := by
    rw [hγ', phi43Group_iPsiCube, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (phi43_poly_one_mem κ)
  have hcor_iPsiCube_pi :
      Z.pi x (Z.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1) =
        Z'.pi x (Z'.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1) := by
    simp only [map_sub]
    exact congrArg₂ (fun u v : parabolicSemigroup.distributions => u - v)
      hpi_iPsiCube (hiPsiCube x)
  have hact_iPsiCube :
      Z.gammaMap x y (Pi.single .iPsiCube 1) =
        Z'.gammaMap x y (Pi.single .iPsiCube 1) := by
    have h := model_poly_pi_injective_pair N κ Z Z' hZ.1 hZ'.1
      hmem_iPsiCube_g hmem_iPsiCube_h hcor_iPsiCube_pi
    calc
      Z.gammaMap x y (Pi.single .iPsiCube 1) =
          (Z.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1) +
            Pi.single .iPsiCube 1 := by abel
      _ = (Z'.gammaMap x y (Pi.single .iPsiCube 1) - Pi.single .iPsiCube 1) +
            Pi.single .iPsiCube 1 := congrArg (fun v => v + Pi.single .iPsiCube 1) h
      _ = Z'.gammaMap x y (Pi.single .iPsiCube 1) := by abel
  have hsi (i : Fin 3) :
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single (.x i) 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single (.x i) 1) := by
    calc
      _ = Z.gammaMap x y (Pi.single (.x i) 1) := by rw [hγ]
      _ = Z'.gammaMap x y (Pi.single (.x i) 1) := hact_x i
      _ = _ := by rw [hγ']
  have hcp :
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1) := by
    calc
      _ = Z.gammaMap x y (Pi.single .iPsi 1) := by rw [hγ]
      _ = Z'.gammaMap x y (Pi.single .iPsi 1) := hact_iPsi
      _ = _ := by rw [hγ']
  have hcg (i : Fin 3) :
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1) (.x i) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsi 1) (.x i) := by
    exact congrFun hcp (.x i)
  have hcs :
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiSq 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiSq 1) := by
    calc
      _ = Z.gammaMap x y (Pi.single .iPsiSq 1) := by rw [hγ]
      _ = Z'.gammaMap x y (Pi.single .iPsiSq 1) := hact_iPsiSq
      _ = _ := by rw [hγ']
  have hcc :
      (Phi43.phi43StructureGroupElement g :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiCube 1) =
      (Phi43.phi43StructureGroupElement h :
        (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiCube 1) := by
    calc
      _ = Z.gammaMap x y (Pi.single .iPsiCube 1) := by rw [hγ]
      _ = Z'.gammaMap x y (Pi.single .iPsiCube 1) := hact_iPsiCube
      _ = _ := by rw [hγ']
  exact phi43RelevantParameters_eq_of_actions hsi hcp hcg hcs hcc

theorem canonicalModels_relevant_parameters_eq_weighted (N : ℕ) (κ : Phi43.Kappa)
    (noise : Phi43.CanonicalNoise) (C : Phi43.RenormalisationConstants)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Phi43.Statements.IsRenormalisedCanonicalModel N κ noise C Z')
    (x y : ParabolicSpace) (g h : Phi43.G)
    (hg : Phi43.phi43StructureGroupElement g = ↑(Z.gamma x y))
    (hh : Phi43.phi43StructureGroupElement h = ↑(Z'.gamma x y)) :
    (∀ i : Fin 3, g.shift i.succ = h.shift i.succ) ∧
      g.cPsi = h.cPsi ∧ (∀ i : Fin 3, g.cPsiGrad i = h.cPsiGrad i) ∧
        g.cPsiSq = h.cPsiSq ∧ g.cPsiCube = h.cPsiCube := by
  exact canonicalModels_relevant_parameters_eq N κ noise C Z Z' hZ hZ' x y g h hg hh

theorem canonicalModels_pi_polynomial_subspace_eq_weighted
    (N : ℕ) (κ : Phi43.Kappa)
    (Z Z' : Model (Phi43.phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Z.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    (hZ' : Z'.IsRealisingP (annKernel0C N) (Phi43.gamma κ)
      (Phi43.phi43PolynomialSector κ) Phi43.phi43AbstractIntegration
      Phi43.phi43IntegrationSector)
    {x : ParabolicSpace} {a : Phi43.Symbol → ℝ}
    (ha : a ∈ (Phi43.phi43PolynomialSector κ).subspace) :
    Z.pi x a = Z'.pi x a := by
  exact model_pi_eq_on_polynomial_subspace N κ Z Z' hZ hZ' ha

theorem phi43Polynomial_one_mem (κ : Phi43.Kappa) :
    (Pi.single .one 1 : Phi43.Symbol → ℝ) ∈
      (Phi43.phi43PolynomialSector κ).subspace := by
  exact phi43_poly_one_mem κ

theorem phi43Polynomial_x_mem (κ : Phi43.Kappa) (i : Fin 3) :
    (Pi.single (.x i) 1 : Phi43.Symbol → ℝ) ∈
      (Phi43.phi43PolynomialSector κ).subspace := by
  exact phi43_poly_x_mem κ i

theorem phi43StructureGroupElement_single_psiX (g : Phi43.G) (i : Fin 3) :
    (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single (.psiX i) 1) =
      (Pi.single (.psiX i) 1 : Phi43.Symbol → ℝ) +
        g.shift i.succ • (Pi.single .psi 1 : Phi43.Symbol → ℝ) := by
  exact phi43Group_psiX g i

theorem phi43StructureGroupElement_single_iPsiPsi (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiPsi 1) =
      (Pi.single .iPsiPsi 1 : Phi43.Symbol → ℝ) + g.cPsi • (Pi.single .psi 1 : Phi43.Symbol → ℝ) +
        ∑ i, g.cPsiGrad i • (Pi.single (.psiX i) 1 : Phi43.Symbol → ℝ) := by
  exact phi43Group_iPsiPsi g

theorem phi43StructureGroupElement_single_iPsiPsiSq (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiPsiSq 1) =
      (Pi.single .iPsiPsiSq 1 : Phi43.Symbol → ℝ) +
        g.cPsi • (Pi.single .psiSq 1 : Phi43.Symbol → ℝ) +
        ∑ i, g.cPsiGrad i • (Pi.single (.psiSqX i) 1 : Phi43.Symbol → ℝ) := by
  exact phi43Group_iPsiPsiSq g

theorem phi43StructureGroupElement_single_iPsiSqPsi (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiSqPsi 1) =
      (Pi.single .iPsiSqPsi 1 : Phi43.Symbol → ℝ) +
        g.cPsiSq • (Pi.single .psi 1 : Phi43.Symbol → ℝ) := by
  exact phi43Group_iPsiSqPsi g

theorem phi43StructureGroupElement_single_iPsiCubeSq (g : Phi43.G) :
    (Phi43.phi43StructureGroupElement g :
      (Phi43.Symbol → ℝ) →ₗ[ℝ] (Phi43.Symbol → ℝ)) (Pi.single .iPsiCubeSq 1) =
      (Pi.single .iPsiCubeSq 1 : Phi43.Symbol → ℝ) +
        (2 * g.cPsiCube) • (Pi.single .iPsiCube 1 : Phi43.Symbol → ℝ) +
        (g.cPsiCube ^ 2) • (Pi.single .one 1 : Phi43.Symbol → ℝ) := by
  exact phi43Group_iPsiCubeSq g

end RegularityStructures

end
