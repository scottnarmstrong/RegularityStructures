/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalGammaActionBounds
import Mathlib.Tactic.Linarith

/-!
# Lipschitz dependence of the finite structure-group action on its parameters

Two-model version of `gammaStructureBasis_weighted_bound`: if the five parameters of two group
elements `g, g'` obey the size bounds with constant `A` and their differences obey the weighted
bounds with constant `Δ`, then every entry of `structureBasisAction g τ - structureBasisAction g' τ`
is bounded by `oldGammaDiffConst A * Δ * d ^ (deg τ - deg σ)`.
-/

public noncomputable section

namespace RegularityStructures.Phi43.Restart

/-- The constant of the Lipschitz bound of all entries of the structure-group action. -/
@[expose] def oldGammaDiffConst (A : ℝ) : ℝ :=
  4 + 8 * (Fintype.card Symbol : ℝ) ^ 2 * (1 + 4 * A) +
    12 * ((Fintype.card Symbol : ℝ) ^ 2) ^ 2 * (1 + 4 * A) ^ 2

theorem oldGammaDiffConst_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ oldGammaDiffConst A := by
  unfold oldGammaDiffConst; positivity

private theorem multiply_sub_left (v w z : T) : (v - w) * z = v * z - w * z := by
  rw [sub_eq_add_neg, multiply_add_left, multiply_neg_left, ← sub_eq_add_neg]

private theorem multiply_sub_right (v w z : T) : v * (w - z) = v * w - v * z := by
  rw [sub_eq_add_neg, multiply_add_right, multiply_neg_right, ← sub_eq_add_neg]

private theorem product_diff_bound (κ : Kappa) {d α β D₁ D₂ B A' : ℝ} (hd : 0 < d)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hB : 0 ≤ B) (hA' : 0 ≤ A') {a a' b b' : T}
    (hda : ∀ σ, |(a - a') σ| ≤ D₁ * d ^ (α - homogeneity κ σ))
    (hb : ∀ σ, |b σ| ≤ B * d ^ (β - homogeneity κ σ))
    (ha' : ∀ σ, |a' σ| ≤ A' * d ^ (α - homogeneity κ σ))
    (hdb : ∀ σ, |(b - b') σ| ≤ D₂ * d ^ (β - homogeneity κ σ)) (σ : Symbol) :
    |(a * b - a' * b') σ| ≤
      ((Fintype.card Symbol : ℝ) ^ 2 * D₁ * B + (Fintype.card Symbol : ℝ) ^ 2 * A' * D₂) *
        d ^ (α + β - homogeneity κ σ) := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by
    rw [multiply_sub_left, multiply_sub_right]; abel
  rw [h]
  exact gammaWeighted_add_bound κ (a := (a - a') * b) (b := a' * (b - b'))
    (fun σ => by simpa using gammaWeighted_multiply_bound κ hd hD₁ hB hda hb σ)
    (fun σ => by simpa using gammaWeighted_multiply_bound κ hd hA' hD₂ ha' hdb σ) σ

private theorem row_diff_bound (κ : Kappa) (g g' : G) {d Δ : ℝ}
    (hd : 0 < d) (hΔ : 0 ≤ Δ)
    (dp : |g.cPsi - g'.cPsi| ≤ Δ * d ^ homogeneity κ .iPsi)
    (dpg : ∀ i, |g.cPsiGrad i - g'.cPsiGrad i| ≤ Δ * d ^ (homogeneity κ .iPsi - 1))
    (τ υ : Symbol) (X : Fin 3 → Symbol)
    (he : homogeneity κ τ - homogeneity κ υ = homogeneity κ .iPsi)
    (heX : ∀ i, homogeneity κ τ - homogeneity κ (X i) = homogeneity κ .iPsi - 1)
    (σ : Symbol) :
    |((basis τ + g.cPsi • basis υ + ∑ i : Fin 3, g.cPsiGrad i • basis (X i)) -
      (basis τ + g'.cPsi • basis υ + ∑ i : Fin 3, g'.cPsiGrad i • basis (X i))) σ| ≤
      (4 * Δ) * d ^ (homogeneity κ τ - homogeneity κ σ) := by
  have h : (basis τ + g.cPsi • basis υ + ∑ i : Fin 3, g.cPsiGrad i • basis (X i)) -
      (basis τ + g'.cPsi • basis υ + ∑ i : Fin 3, g'.cPsiGrad i • basis (X i)) =
      (g.cPsi - g'.cPsi) • basis υ +
        ∑ i : Fin 3, (g.cPsiGrad i - g'.cPsiGrad i) • basis (X i) := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [h]
  have ht (σ : Symbol) : |((g.cPsi - g'.cPsi) • basis υ) σ| ≤
      Δ * d ^ (homogeneity κ τ - homogeneity κ σ) :=
    gammaWeightedBasis_bound κ hd hΔ υ (by rwa [he]) σ
  have hg (i : Fin 3) (σ : Symbol) :
      |((g.cPsiGrad i - g'.cPsiGrad i) • basis (X i)) σ| ≤
        Δ * d ^ (homogeneity κ τ - homogeneity κ σ) :=
    gammaWeightedBasis_bound κ hd hΔ (X i) (by rw [heX]; exact dpg i) σ
  have hsum (σ : Symbol) :
      |(∑ i : Fin 3, (g.cPsiGrad i - g'.cPsiGrad i) • basis (X i)) σ| ≤
        (3 * Δ) * d ^ (homogeneity κ τ - homogeneity κ σ) := by
    simpa using gammaWeighted_sum_bound κ Finset.univ (fun _ : Fin 3 => Δ)
      (fun i => (g.cPsiGrad i - g'.cPsiGrad i) • basis (X i)) (fun i _ => hg i) σ
  simpa only [show Δ + 3 * Δ = 4 * Δ by ring] using
    gammaWeighted_add_bound κ ht hsum σ

/-- **Lipschitz bound** for every entry of the finite structure-group action. -/
theorem gammaStructureBasis_weighted_bound_diff (κ : Kappa) (g g' : G) {d A Δ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hΔ : 0 ≤ Δ)
    (hx : ∀ i, |g.shift i| ≤ A * d ^ (parabolicWeight i : ℝ))
    (hp : |g.cPsi| ≤ A * d ^ homogeneity κ .iPsi)
    (hpg : ∀ i, |g.cPsiGrad i| ≤ A * d ^ (homogeneity κ .iPsi - 1))
    (hs : |g.cPsiSq| ≤ A * d ^ homogeneity κ .iPsiSq)
    (hc : |g.cPsiCube| ≤ A * d ^ homogeneity κ .iPsiCube)
    (hx' : ∀ i, |g'.shift i| ≤ A * d ^ (parabolicWeight i : ℝ))
    (hp' : |g'.cPsi| ≤ A * d ^ homogeneity κ .iPsi)
    (hpg' : ∀ i, |g'.cPsiGrad i| ≤ A * d ^ (homogeneity κ .iPsi - 1))
    (hs' : |g'.cPsiSq| ≤ A * d ^ homogeneity κ .iPsiSq)
    (hc' : |g'.cPsiCube| ≤ A * d ^ homogeneity κ .iPsiCube)
    (dx : ∀ i, |g.shift i - g'.shift i| ≤ Δ * d ^ (parabolicWeight i : ℝ))
    (dp : |g.cPsi - g'.cPsi| ≤ Δ * d ^ homogeneity κ .iPsi)
    (dpg : ∀ i, |g.cPsiGrad i - g'.cPsiGrad i| ≤ Δ * d ^ (homogeneity κ .iPsi - 1))
    (ds : |g.cPsiSq - g'.cPsiSq| ≤ Δ * d ^ homogeneity κ .iPsiSq)
    (dc : |g.cPsiCube - g'.cPsiCube| ≤ Δ * d ^ homogeneity κ .iPsiCube)
    (τ σ : Symbol) :
    |structureBasisAction g τ σ - structureBasisAction g' τ σ| ≤
      oldGammaDiffConst A * Δ * d ^ (homogeneity κ τ - homogeneity κ σ) := by
  let P : ℝ := 1 + 4 * A
  let n : ℝ := (Fintype.card Symbol : ℝ) ^ 2
  let K : ℝ := oldGammaDiffConst A
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hn : 0 ≤ n := sq_nonneg _
  have hK : K = 4 + 8 * n * P + 12 * n ^ 2 * P ^ 2 := rfl
  have hnP : 0 ≤ n * P := mul_nonneg hn hP
  have hnP2 : 0 ≤ n ^ 2 * P ^ 2 := by positivity
  have hΔ4 : 0 ≤ 4 * Δ := by linarith
  have hprim := gammaPrimitiveAction_weighted_bound κ g hd hA hx hp hpg hs hc
  have hprim' := gammaPrimitiveAction_weighted_bound κ g' hd hA hx' hp' hpg' hs' hc'
  have hbase (υ σ : Symbol) : |basis υ σ| ≤ 1 * d ^ (homogeneity κ υ - homogeneity κ σ) := by
    simpa only [one_smul] using gammaWeightedBasis_bound κ (α := homogeneity κ υ)
      (c := 1) hd (by norm_num : (0 : ℝ) ≤ 1) υ (by simp) σ
  have hconst (υ : Symbol) (c c' : ℝ) (hh : |c - c'| ≤ Δ * d ^ homogeneity κ υ)
      (σ : Symbol) :
      |((basis υ + c • basis .one) - (basis υ + c' • basis .one)) σ| ≤
        (4 * Δ) * d ^ (homogeneity κ υ - homogeneity κ σ) := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    exact (gammaWeightedBasis_bound κ hd hΔ .one
      (by simpa only [homogeneity, sub_zero] using hh) σ).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le _))
  have hzero (υ σ : Symbol) :
      |((primitiveAction g υ) - (primitiveAction g' υ)) σ| ≤
        (4 * Δ) * d ^ (homogeneity κ υ - homogeneity κ σ) := by
    cases υ with
    | one => simp only [primitiveAction, sub_self, Finsupp.zero_apply, abs_zero]
             exact mul_nonneg hΔ4 (Real.rpow_nonneg hd.le _)
    | noise => simp only [primitiveAction, sub_self, Finsupp.zero_apply, abs_zero]
               exact mul_nonneg hΔ4 (Real.rpow_nonneg hd.le _)
    | psi => simp only [primitiveAction, sub_self, Finsupp.zero_apply, abs_zero]
             exact mul_nonneg hΔ4 (Real.rpow_nonneg hd.le _)
    | x0 => exact hconst .x0 (g.shift 0) (g'.shift 0)
              (by simpa [homogeneity, parabolicWeight] using dx 0) σ
    | x i =>
        exact hconst (.x i) (g.shift i.succ) (g'.shift i.succ)
          (by
            have hh := dx i.succ
            fin_cases i <;> simpa [homogeneity, parabolicWeight] using hh) σ
    | iPsiSq => exact hconst .iPsiSq g.cPsiSq g'.cPsiSq ds σ
    | iPsiCube => exact hconst .iPsiCube g.cPsiCube g'.cPsiCube dc σ
    | iPsi =>
        exact row_diff_bound κ g g' hd hΔ dp dpg .iPsi .one Symbol.x
          (by simp only [homogeneity]; ring) (fun i => by simp only [homogeneity]) σ
    | _ => simp only [primitiveAction, sub_self, Finsupp.zero_apply, abs_zero]
           exact mul_nonneg hΔ4 (Real.rpow_nonneg hd.le _)
  have hprod (a b σ : Symbol) :
      |(primitiveAction g a * primitiveAction g b) σ| ≤
        (n * P ^ 2) * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) := by
    convert gammaWeighted_multiply_bound κ hd hP hP (hprim a) (hprim b) σ using 1
    dsimp [n, P]
    ring
  have hprod' (a b σ : Symbol) :
      |(primitiveAction g' a * primitiveAction g' b) σ| ≤
        (n * P ^ 2) * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) := by
    convert gammaWeighted_multiply_bound κ hd hP hP (hprim' a) (hprim' b) σ using 1
    dsimp [n, P]
    ring
  have hdprod (a b σ : Symbol) :
      |(primitiveAction g a * primitiveAction g b -
          primitiveAction g' a * primitiveAction g' b) σ| ≤
        (8 * n * P * Δ) * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) := by
    convert product_diff_bound κ hd hΔ4 hΔ4 hP hP (hzero a) (hprim b) (hprim' a)
      (hzero b) σ using 1
    dsimp [n, P]
    ring
  have hdtriple (a b c σ : Symbol) :
      |((primitiveAction g a * primitiveAction g b) * primitiveAction g c -
          (primitiveAction g' a * primitiveAction g' b) * primitiveAction g' c) σ| ≤
        (12 * n ^ 2 * P ^ 2 * Δ) * d ^
          ((homogeneity κ a + homogeneity κ b) + homogeneity κ c - homogeneity κ σ) := by
    convert product_diff_bound κ hd (by positivity) hΔ4 hP (mul_nonneg hn (sq_nonneg P))
      (hdprod a b) (hprim c) (hprod' a b) (hzero c) σ using 1
    dsimp [n, P]
    ring
  have hdtriple' (a b c σ : Symbol) :
      |(primitiveAction g a * (primitiveAction g b * primitiveAction g c) -
          primitiveAction g' a * (primitiveAction g' b * primitiveAction g' c)) σ| ≤
        (12 * n ^ 2 * P ^ 2 * Δ) * d ^
          (homogeneity κ a + (homogeneity κ b + homogeneity κ c) - homogeneity κ σ) := by
    convert product_diff_bound κ hd hΔ4 (by positivity) (mul_nonneg hn (sq_nonneg P)) hP
      (hzero a) (hprod b c) (hprim' a) (hdprod b c) σ using 1
    dsimp [n, P]
    ring
  have lift1 (a σ : Symbol) :
      |(primitiveAction g a - primitiveAction g' a) σ| ≤
        K * Δ * d ^ (homogeneity κ a - homogeneity κ σ) := by
    refine (hzero a σ).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
    rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]
  have lift2 (a b σ : Symbol) :
      |(primitiveAction g a * primitiveAction g b -
          primitiveAction g' a * primitiveAction g' b) σ| ≤
        K * Δ * d ^ (homogeneity κ a + homogeneity κ b - homogeneity κ σ) := by
    refine (hdprod a b σ).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
    rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]
  have lift3 (a b c σ : Symbol) :
      |((primitiveAction g a * primitiveAction g b) * primitiveAction g c -
          (primitiveAction g' a * primitiveAction g' b) * primitiveAction g' c) σ| ≤
        K * Δ * d ^ ((homogeneity κ a + homogeneity κ b) + homogeneity κ c -
          homogeneity κ σ) := by
    refine (hdtriple a b c σ).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
    rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]
  have lift3' (a b c σ : Symbol) :
      |(primitiveAction g a * (primitiveAction g b * primitiveAction g c) -
          primitiveAction g' a * (primitiveAction g' b * primitiveAction g' c)) σ| ≤
        K * Δ * d ^ (homogeneity κ a + (homogeneity κ b + homogeneity κ c) -
          homogeneity κ σ) := by
    refine (hdtriple' a b c σ).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
    rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]
  rw [← Finsupp.sub_apply]
  change |(structureBasisAction g τ - structureBasisAction g' τ) σ| ≤
    K * Δ * d ^ (homogeneity κ τ - homogeneity κ σ)
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
      simp only [structureBasisAction]
      convert lift2 .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiCube =>
      simp only [structureBasisAction]
      convert lift3 .psi .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiX i =>
      simp only [structureBasisAction]
      convert lift2 .psi (.x i) σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | psiSqX i =>
      simp only [structureBasisAction]
      convert lift3' (.x i) .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiSqPsi =>
      simp only [structureBasisAction]
      convert lift2 .iPsiSq .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiSqPsiSq =>
      simp only [structureBasisAction]
      convert lift3' .iPsiSq .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubePsi =>
      simp only [structureBasisAction]
      convert lift2 .iPsiCube .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubePsiSq =>
      simp only [structureBasisAction]
      convert lift3' .iPsiCube .psi .psi σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiCubeSq =>
      simp only [structureBasisAction]
      convert lift2 .iPsiCube .iPsiCube σ using 1
      congr 2
      dsimp only [homogeneity]
      ring
  | iPsiPsi =>
      refine (row_diff_bound κ g g' hd hΔ dp dpg .iPsiPsi .psi Symbol.psiX
        (by simp only [homogeneity]; ring) (fun i => by simp only [homogeneity]; ring) σ).trans
          (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
      rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]
  | iPsiPsiSq =>
      refine (row_diff_bound κ g g' hd hΔ dp dpg .iPsiPsiSq .psiSq Symbol.psiSqX
        (by simp only [homogeneity]; ring) (fun i => by simp only [homogeneity]; ring) σ).trans
          (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _))
      rw [hK]; linarith [mul_nonneg hnP hΔ, mul_nonneg hnP2 hΔ]

end RegularityStructures.Phi43.Restart

end
