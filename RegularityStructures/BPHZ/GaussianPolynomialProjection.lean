/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialGenerator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal projection onto polynomials of bounded degree

Polynomials of total degree at most `m` form a finite-dimensional subspace of `L²(γ)`.  Hence every
polynomial `f` splits as `f = h + (f - h)` with `h` of degree at most `m` and `f - h` orthogonal in
`L²(γ)` to all polynomials of degree at most `m` (`exists_orthogonal_part`).
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

/-- Polynomials as elements of `L²(γ)`. -/
private noncomputable def polyToL2 (n : ℕ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] Lp ℝ 2 (standardGaussianMeasure n) where
  toFun p := (memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤)).toLp
    (fun x => eval x p)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_eval_standardGaussianMeasure (p + q) (by simp : (2 : ENNReal) ≠ ⊤)),
      Lp.coeFn_add
        ((memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤)).toLp
          (fun x => eval x p))
        ((memLp_eval_standardGaussianMeasure q (by simp : (2 : ENNReal) ≠ ⊤)).toLp
          (fun x => eval x q)),
      MemLp.coeFn_toLp (memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤)),
      MemLp.coeFn_toLp (memLp_eval_standardGaussianMeasure q (by simp : (2 : ENNReal) ≠ ⊤))]
      with x h1 h2 h3 h4
    rw [h2, Pi.add_apply, h1, h3, h4, map_add]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_eval_standardGaussianMeasure (c • p) (by simp : (2 : ENNReal) ≠ ⊤)),
      Lp.coeFn_smul c
        ((memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤)).toLp
          (fun x => eval x p)),
      MemLp.coeFn_toLp (memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤))]
      with x h1 h2 h3
    rw [RingHom.id_apply, h2, Pi.smul_apply, h1, h3, smul_eval, smul_eq_mul]

private theorem inner_polyToL2 (p q : MvPolynomial (Fin n) ℝ) :
    inner ℝ (polyToL2 n p) (polyToL2 n q) = gaussExp (p * q) := by
  rw [L2.inner_def]
  unfold gaussExp
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_eval_standardGaussianMeasure p
      (by simp : (2 : ENNReal) ≠ ⊤)),
    MemLp.coeFn_toLp (memLp_eval_standardGaussianMeasure q (by simp : (2 : ENNReal) ≠ ⊤))]
    with x h1 h2
  change inner ℝ ((polyToL2 n p) x) ((polyToL2 n q) x) = _
  change inner ℝ (((memLp_eval_standardGaussianMeasure p (by simp : (2 : ENNReal) ≠ ⊤)).toLp
    (fun x => eval x p)) x) (((memLp_eval_standardGaussianMeasure q
      (by simp : (2 : ENNReal) ≠ ⊤)).toLp (fun x => eval x q)) x) = _
  rw [h1, h2, map_mul, real_inner_eq_re_inner]
  simp [mul_comm]

/-- Every polynomial splits into a part of degree at most `m` and a part orthogonal in `L²(γ)`
to all polynomials of degree at most `m`. -/
theorem exists_orthogonal_part (m : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    ∃ h : MvPolynomial (Fin n) ℝ, h.totalDegree ≤ m ∧
      ∀ u : MvPolynomial (Fin n) ℝ, u.totalDegree ≤ m → gaussExp ((f - h) * u) = 0 := by
  let K : Submodule ℝ (Lp ℝ 2 (standardGaussianMeasure n)) :=
    (restrictTotalDegree (Fin n) ℝ m).map (polyToL2 n)
  have : Module.Finite ℝ K := inferInstance
  have : K.HasOrthogonalProjection := inferInstance
  have hmem : K.starProjection (polyToL2 n f) ∈ K := Submodule.starProjection_apply_mem K _
  obtain ⟨h, hh, hhK⟩ := Submodule.mem_map.mp hmem
  refine ⟨h, (mem_restrictTotalDegree _ _ _).mp hh, fun u hu => ?_⟩
  have hu' : polyToL2 n u ∈ K :=
    Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).mpr hu)
  have h0 := Submodule.starProjection_inner_eq_zero (K := K) (polyToL2 n f) _ hu'
  rw [← hhK, ← map_sub, inner_polyToL2] at h0
  exact h0

end RegularityStructures

end
