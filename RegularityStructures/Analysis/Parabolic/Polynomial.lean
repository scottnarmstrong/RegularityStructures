/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Parabolically weighted polynomials on `ℝ × ℝ³`

Polynomials in the four coordinates `(z₀, z₁, z₂, z₃)` of `ParabolicSpace`, graded by the parabolic
weights `𝔰 = (2, 1, 1, 1)`. A weighted homogeneous polynomial of degree `n` scales like `c ^ n`
under `parabolicDilate c`, and a monomial of degree `n` is bounded by `‖z‖_𝔰 ^ n`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The parabolic weights `𝔰 = (2, 1, 1, 1)`. -/
def parabolicWeight : Fin 4 → ℕ := ![2, 1, 1, 1]

/-- The four coordinates `(z₀, z₁, z₂, z₃)` of a point of parabolic space. -/
def parabolicCoords (z : ParabolicSpace) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

/-- Evaluation of a polynomial in four variables at a point of parabolic space. -/
def evalParabolic (p : MvPolynomial (Fin 4) ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords z) p

end RegularityStructures

end

public section

namespace RegularityStructures

theorem weight_parabolicWeight (k : Fin 4 →₀ ℕ) :
    Finsupp.weight parabolicWeight k = 2 * k 0 + k 1 + k 2 + k 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, parabolicWeight]
  ring

theorem parabolicCoords_parabolicDilate (c : ℝ) (z : ParabolicSpace) :
    parabolicCoords (parabolicDilate c z) = fun i => c ^ parabolicWeight i * parabolicCoords z i := by
  funext i
  fin_cases i <;> simp [parabolicCoords, parabolicDilate, parabolicWeight, sq]

theorem evalParabolic_parabolicDilate {p : MvPolynomial (Fin 4) ℝ} {n : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous parabolicWeight p n) (c : ℝ) (z : ParabolicSpace) :
    evalParabolic p (parabolicDilate c z) = c ^ n * evalParabolic p z := by
  unfold evalParabolic
  rw [parabolicCoords_parabolicDilate, MvPolynomial.eval_eq, MvPolynomial.eval_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight parabolicWeight d = n := hp (MvPolynomial.mem_support_iff.1 hd)
  have : ∏ i, (c ^ parabolicWeight i * parabolicCoords z i) ^ d i =
      c ^ n * ∏ i, parabolicCoords z i ^ d i := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, ← hw, Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [mul_comm]
    · simp
  have hf : ∀ g : Fin 4 → ℝ, ∏ i ∈ d.support, g i ^ d i = ∏ i, g i ^ d i := fun g =>
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
      simp [Finsupp.notMem_support_iff.1 hi]
  rw [hf, hf, this]
  ring

theorem continuous_evalParabolic (p : MvPolynomial (Fin 4) ℝ) :
    Continuous (evalParabolic p) := by
  unfold evalParabolic
  refine (MvPolynomial.continuous_eval p).comp ?_
  unfold parabolicCoords
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

theorem abs_evalParabolic_monomial_le (k : Fin 4 →₀ ℕ) (z : ParabolicSpace) :
    |evalParabolic (MvPolynomial.monomial k 1) z| ≤ parabolicNorm z ^ (2 * k 0 + k 1 + k 2 + k 3) := by
  unfold evalParabolic
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), one_mul]
  simp only [Fin.prod_univ_four, abs_mul, abs_pow]
  have hn := parabolicNorm_nonneg z
  have h0 : |z.1| ≤ parabolicNorm z ^ 2 := by
    have : Real.sqrt |z.1| ≤ parabolicNorm z := by
      unfold parabolicNorm
      have : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    calc |z.1| = Real.sqrt |z.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ _ := by gcongr
  have hi : ∀ i, |z.2 i| ≤ parabolicNorm z := fun i => by
    unfold parabolicNorm
    have : |z.2 i| ≤ ∑ j, |z.2 j| :=
      Finset.single_le_sum (f := fun j => |z.2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [Real.sqrt_nonneg |z.1|]
  simp only [parabolicCoords]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have e : parabolicNorm z ^ (2 * k 0 + k 1 + k 2 + k 3) =
      (parabolicNorm z ^ 2) ^ k 0 * parabolicNorm z ^ k 1 * parabolicNorm z ^ k 2 *
        parabolicNorm z ^ k 3 := by
    rw [← pow_mul]
    simp only [pow_add]
  rw [e]
  gcongr
  · exact hi 0
  · exact hi 1
  · exact hi 2

end RegularityStructures

end
