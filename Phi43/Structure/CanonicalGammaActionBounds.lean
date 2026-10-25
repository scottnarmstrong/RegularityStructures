/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalGammaWeightedAlgebra
public import RegularityStructures.Analysis.Parabolic.Polynomial
import Mathlib.Tactic.Linarith

/-!
# Weighted bounds for the finite structure-group action

Algebraic assembly of the primitive character estimates used by Hairer
[Hai14, Proposition 8.27] for the canonical model.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- The primitive action has weighted coefficient bounds derived solely
from the homogeneously weighted primitive character coefficients. -/
theorem gammaPrimitiveAction_weighted_bound (κ : Kappa) (g : G) {d A : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A)
    (hx : ∀ i, |g.shift i| ≤ A * d ^ (parabolicWeight i : ℝ))
    (hp : |g.cPsi| ≤ A * d ^ homogeneity κ .iPsi)
    (hpg : ∀ i, |g.cPsiGrad i| ≤ A * d ^ (homogeneity κ .iPsi - 1))
    (hs : |g.cPsiSq| ≤ A * d ^ homogeneity κ .iPsiSq)
    (hc : |g.cPsiCube| ≤ A * d ^ homogeneity κ .iPsiCube)
    (τ σ : Symbol) :
    |primitiveAction g τ σ| ≤ (1 + 4 * A) * d ^ (homogeneity κ τ - homogeneity κ σ) := by
  have hbase (υ σ : Symbol) : |basis υ σ| ≤ 1 * d ^ (homogeneity κ υ - homogeneity κ σ) := by
    simpa only [one_smul] using gammaWeightedBasis_bound κ (α := homogeneity κ υ)
      (c := 1) hd (by norm_num : (0 : ℝ) ≤ 1) υ (by simp) σ
  have hsmall : 1 ≤ 1 + 4 * A := by linarith
  have htwo : 1 + A ≤ 1 + 4 * A := by linarith
  have hzero : 0 ≤ 1 + 4 * A := by linarith
  have hconst (υ : Symbol) (c : ℝ) (hh : |c| ≤ A * d ^ homogeneity κ υ) (σ : Symbol) :
      |(basis υ + c • basis .one) σ| ≤ (1 + 4 * A) *
        d ^ (homogeneity κ υ - homogeneity κ σ) := by
    have ht (σ : Symbol) : |(c • basis .one) σ| ≤ A * d ^ (homogeneity κ υ - homogeneity κ σ) :=
      gammaWeightedBasis_bound κ hd hA .one (by simpa only [homogeneity, sub_zero] using hh) σ
    exact (gammaWeighted_add_bound κ (hbase υ) ht σ).trans
      (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hd.le _))
  cases τ with
  | one =>
      exact (hbase .one σ).trans
        (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le _))
  | noise =>
      exact (hbase .noise σ).trans
        (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le _))
  | psi =>
      exact (hbase .psi σ).trans
        (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le _))
  | x0 => exact hconst .x0 (g.shift 0) (by simpa [homogeneity, parabolicWeight] using hx 0) σ
  | x i =>
      exact hconst (.x i) (g.shift i.succ)
        (by
          have hh := hx i.succ
          fin_cases i <;> simpa [homogeneity, parabolicWeight] using hh) σ
  | iPsiSq => exact hconst .iPsiSq g.cPsiSq hs σ
  | iPsiCube => exact hconst .iPsiCube g.cPsiCube hc σ
  | iPsi =>
      have ht (σ : Symbol) : |(g.cPsi • basis .one) σ| ≤
          A * d ^ (homogeneity κ .iPsi - homogeneity κ σ) :=
        gammaWeightedBasis_bound κ hd hA .one (by simpa only [homogeneity, sub_zero] using hp) σ
      have hgrad (i : Fin 3) (σ : Symbol) : |(g.cPsiGrad i • basis (.x i)) σ| ≤
          A * d ^ (homogeneity κ .iPsi - homogeneity κ σ) :=
        gammaWeightedBasis_bound κ hd hA (.x i) (by simpa only [homogeneity] using hpg i) σ
      have hsum (σ : Symbol) : |(∑ i : Fin 3, g.cPsiGrad i • basis (.x i)) σ| ≤
          (3 * A) * d ^ (homogeneity κ .iPsi - homogeneity κ σ) := by
        simpa using gammaWeighted_sum_bound κ Finset.univ (fun _ : Fin 3 => A)
          (fun i => g.cPsiGrad i • basis (.x i)) (fun i _ => hgrad i) σ
      change |(basis .iPsi + g.cPsi • basis .one + ∑ i : Fin 3,
        g.cPsiGrad i • basis (.x i)) σ| ≤ _
      simpa only [show (1 + A) + 3 * A = 1 + 4 * A by ring] using
        gammaWeighted_add_bound κ (gammaWeighted_add_bound κ (hbase .iPsi) ht) hsum σ
  | _ =>
      simp only [primitiveAction, Finsupp.zero_apply, abs_zero]
      exact mul_nonneg hzero (Real.rpow_nonneg hd.le _)

private theorem integrated_row_bound (κ : Kappa) (g : G) {d A : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A)
    (hp : |g.cPsi| ≤ A * d ^ homogeneity κ .iPsi)
    (hpg : ∀ i, |g.cPsiGrad i| ≤ A * d ^ (homogeneity κ .iPsi - 1))
    (τ υ : Symbol) (X : Fin 3 → Symbol)
    (he : homogeneity κ τ - homogeneity κ υ = homogeneity κ .iPsi)
    (heX : ∀ i, homogeneity κ τ - homogeneity κ (X i) = homogeneity κ .iPsi - 1)
    (σ : Symbol) :
    |(basis τ + g.cPsi • basis υ + ∑ i : Fin 3, g.cPsiGrad i • basis (X i)) σ| ≤
      (1 + 4 * A) * d ^ (homogeneity κ τ - homogeneity κ σ) := by
  have hb (σ : Symbol) : |basis τ σ| ≤ 1 * d ^ (homogeneity κ τ - homogeneity κ σ) := by
    simpa only [one_smul] using gammaWeightedBasis_bound κ (α := homogeneity κ τ)
      (c := 1) hd (by norm_num : (0 : ℝ) ≤ 1) τ (by simp) σ
  have ht (σ : Symbol) : |(g.cPsi • basis υ) σ| ≤
      A * d ^ (homogeneity κ τ - homogeneity κ σ) :=
    gammaWeightedBasis_bound κ hd hA υ (by rwa [he]) σ
  have hg (i : Fin 3) (σ : Symbol) : |(g.cPsiGrad i • basis (X i)) σ| ≤
      A * d ^ (homogeneity κ τ - homogeneity κ σ) :=
    gammaWeightedBasis_bound κ hd hA (X i) (by rw [heX]; exact hpg i) σ
  have hsum (σ : Symbol) : |(∑ i : Fin 3, g.cPsiGrad i • basis (X i)) σ| ≤
      (3 * A) * d ^ (homogeneity κ τ - homogeneity κ σ) := by
    simpa using gammaWeighted_sum_bound κ Finset.univ (fun _ : Fin 3 => A)
      (fun i => g.cPsiGrad i • basis (X i)) (fun i _ => hg i) σ
  simpa only [show (1 + A) + 3 * A = 1 + 4 * A by ring] using
    gammaWeighted_add_bound κ (gammaWeighted_add_bound κ hb ht) hsum σ

/-- Every coefficient of the multiplicatively derived finite action obeys
the expected homogeneity bound. The constant depends only on the common
primitive coefficient bound and the finite dimension, not on `g` or `d`. -/
theorem gammaStructureBasis_weighted_bound (κ : Kappa) (g : G) {d A : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A)
    (hx : ∀ i, |g.shift i| ≤ A * d ^ (parabolicWeight i : ℝ))
    (hp : |g.cPsi| ≤ A * d ^ homogeneity κ .iPsi)
    (hpg : ∀ i, |g.cPsiGrad i| ≤ A * d ^ (homogeneity κ .iPsi - 1))
    (hs : |g.cPsiSq| ≤ A * d ^ homogeneity κ .iPsiSq)
    (hc : |g.cPsiCube| ≤ A * d ^ homogeneity κ .iPsiCube)
    (τ σ : Symbol) :
    |structureBasisAction g τ σ| ≤
      ((1 + 4 * A) + (Fintype.card Symbol : ℝ) ^ 2 * (1 + 4 * A) ^ 2 +
        ((Fintype.card Symbol : ℝ) ^ 2) ^ 2 * (1 + 4 * A) ^ 3) *
      d ^ (homogeneity κ τ - homogeneity κ σ) := by
  let P : ℝ := 1 + 4 * A
  let n : ℝ := (Fintype.card Symbol : ℝ) ^ 2
  let C : ℝ := P + n * P ^ 2 + n ^ 2 * P ^ 3
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hn : 0 ≤ n := sq_nonneg _
  have hcost1 : P ≤ C := by
    dsimp [C]
    linarith [mul_nonneg hn (sq_nonneg P), mul_nonneg (sq_nonneg n) (pow_nonneg hP 3)]
  have hcost2 : n * P ^ 2 ≤ C := by
    dsimp [C]
    linarith [mul_nonneg (sq_nonneg n) (pow_nonneg hP 3)]
  have hcost3 : n ^ 2 * P ^ 3 ≤ C := by
    dsimp [C]
    linarith [mul_nonneg hn (sq_nonneg P)]
  have hprim := gammaPrimitiveAction_weighted_bound κ g hd hA hx hp hpg hs hc
  have hprod (a b σ : Symbol) :
      |(primitiveAction g a * primitiveAction g b) σ| ≤
        (n * P ^ 2) * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) := by
    convert gammaWeighted_multiply_bound κ hd hP hP (hprim a) (hprim b) σ using 1
    dsimp [n, P]
    ring
  have htriple (a b c σ : Symbol) :
      |((primitiveAction g a * primitiveAction g b) * primitiveAction g c) σ| ≤
        (n ^ 2 * P ^ 3) * d ^
          ((homogeneity κ a + homogeneity κ b) + homogeneity κ c - homogeneity κ σ) := by
    convert gammaWeighted_multiply_bound κ hd (mul_nonneg hn (sq_nonneg P)) hP
      (hprod a b) (hprim c) σ using 1
    dsimp [n]
    ring
  have htriple' (a b c σ : Symbol) :
      |(primitiveAction g a * (primitiveAction g b * primitiveAction g c)) σ| ≤
        (n ^ 2 * P ^ 3) * d ^
          (homogeneity κ a + (homogeneity κ b + homogeneity κ c) - homogeneity κ σ) := by
    convert gammaWeighted_multiply_bound κ hd hP (mul_nonneg hn (sq_nonneg P))
      (hprim a) (hprod b c) σ using 1
    dsimp [n]
    ring
  have lift1 (a σ : Symbol) : |primitiveAction g a σ| ≤ C *
      d ^ (homogeneity κ a - homogeneity κ σ) :=
    (hprim a σ).trans (mul_le_mul_of_nonneg_right hcost1 (Real.rpow_nonneg hd.le _))
  have lift2 (a b σ : Symbol) : |(primitiveAction g a * primitiveAction g b) σ| ≤
      C * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) :=
    (hprod a b σ).trans (mul_le_mul_of_nonneg_right hcost2 (Real.rpow_nonneg hd.le _))
  have lift3 (a b c σ : Symbol) :
      |((primitiveAction g a * primitiveAction g b) * primitiveAction g c) σ| ≤
        C * d ^ ((homogeneity κ a + homogeneity κ b) + homogeneity κ c - homogeneity κ σ) :=
    (htriple a b c σ).trans (mul_le_mul_of_nonneg_right hcost3 (Real.rpow_nonneg hd.le _))
  have lift3' (a b c σ : Symbol) :
      |(primitiveAction g a * (primitiveAction g b * primitiveAction g c)) σ| ≤
        C * d ^ (homogeneity κ a + (homogeneity κ b + homogeneity κ c) - homogeneity κ σ) :=
    (htriple' a b c σ).trans (mul_le_mul_of_nonneg_right hcost3 (Real.rpow_nonneg hd.le _))
  change |structureBasisAction g τ σ| ≤ C * d ^ (homogeneity κ τ - homogeneity κ σ)
  cases τ with
  | one => exact lift1 .one σ
  | noise => exact lift1 .noise σ
  | x0 => exact lift1 .x0 σ
  | x i => exact lift1 (.x i) σ
  | psi => exact lift1 .psi σ
  | iPsi => exact lift1 .iPsi σ
  | iPsiSq => exact lift1 .iPsiSq σ
  | iPsiCube => exact lift1 .iPsiCube σ
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      simpa only [structureBasisAction, xMulAction_mk, homogeneity,
        show (1 : ℝ) + 1 = 2 by norm_num] using! lift2 (.x i) (.x j) σ
  | psiSq =>
      rw [structureBasisAction]
      convert lift2 .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiCube =>
      rw [structureBasisAction]
      convert lift3 .psi .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiX i =>
      rw [structureBasisAction]
      convert lift2 .psi (.x i) σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiSqX i =>
      rw [structureBasisAction]
      convert lift3' (.x i) .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiSqPsi =>
      rw [structureBasisAction]
      convert lift2 .iPsiSq .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiSqPsiSq =>
      rw [structureBasisAction]
      convert lift3' .iPsiSq .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubePsi =>
      rw [structureBasisAction]
      convert lift2 .iPsiCube .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubePsiSq =>
      rw [structureBasisAction]
      convert lift3' .iPsiCube .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubeSq =>
      rw [structureBasisAction]
      convert lift2 .iPsiCube .iPsiCube σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiPsi =>
      exact (integrated_row_bound κ g hd hA hp hpg .iPsiPsi .psi Symbol.psiX
        (by simp only [homogeneity]; ring) (fun i => by simp only [homogeneity]; ring) σ).trans
          (mul_le_mul_of_nonneg_right hcost1 (Real.rpow_nonneg hd.le _))
  | iPsiPsiSq =>
      exact (integrated_row_bound κ g hd hA hp hpg .iPsiPsiSq .psiSq Symbol.psiSqX
        (by simp only [homogeneity]; ring) (fun i => by simp only [homogeneity]; ring) σ).trans
          (mul_le_mul_of_nonneg_right hcost1 (Real.rpow_nonneg hd.le _))

end RegularityStructures.Phi43

end
