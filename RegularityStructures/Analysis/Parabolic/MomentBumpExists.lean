/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.MomentBump
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
public import RegularityStructures.Analysis.Parabolic.TestFunction
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists
public import RegularityStructures.Abstract.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Bumps with prescribed moments

`exists_moment_bump`: a smooth function supported in the unit parabolic ball whose moments `∫ z^k ψ`,
`|k|_𝔰 < N`, take prescribed values.
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

namespace RegularityStructures

open MeasureTheory Matrix

open scoped ContDiff in
/-- A smooth function supported in the unit parabolic ball whose moments `∫ z^k ψ`, for
`|k|_𝔰 < N`, are prescribed to be `c k`. -/
theorem exists_moment_bump (N : ℕ) (c : PolyIndex N → ℝ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = c k := by
  obtain ⟨φ, hφ, hφint⟩ := exists_mem_testFunctionClass 0
  set χ : ParabolicSpace → ℝ := fun z => φ z ^ 2 with hχdef
  have hχ : ContDiff ℝ ∞ χ := hφ.1.pow 2
  have hsupp : ∀ z, 1 < parabolicNorm z → χ z = 0 := fun z hz => by simp [hχdef, hφ.2.1 z hz]
  have hne : ({z | φ z ≠ 0} : Set ParabolicSpace).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : ∀ z, φ z = 0 := fun z => by
      by_contra hz
      exact (Set.eq_empty_iff_forall_notMem.1 hcon) z hz
    simp [h0] at hφint
  have hU : IsUnit (momentGram N χ).det :=
    isUnit_det_momentGram hχ (fun z => sq_nonneg _) hsupp
      ⟨{z | φ z ≠ 0}, isOpen_ne_fun hφ.1.continuous continuous_const, hne,
        fun z hz => lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))⟩
  set a : PolyIndex N → ℝ := (momentGram N χ)⁻¹ *ᵥ c with ha
  have hGa : momentGram N χ *ᵥ a = c := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  refine ⟨fun z => (∑ j, a j * momentMono j.1 z) * χ z, ?_, ?_, fun k => ?_⟩
  · refine (ContDiff.sum fun j _ => ?_).mul hχ
    exact contDiff_const.mul (contDiff_momentMono j.1)
  · intro z hz
    simp [hsupp z hz]
  · have hint : ∀ j : PolyIndex N, Integrable fun z => a j * (momentMono k.1 z * momentMono j.1 z * χ z) :=
      fun j => (integrable_momentMono_mul_mul hχ hsupp k.1 j.1).const_mul (a j)
    have : ∀ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ((∑ j, a j * momentMono j.1 z) * χ z) =
        ∑ j, a j * (momentMono k.1 z * momentMono j.1 z * χ z) := fun z => by
      change momentMono k.1 z * _ = _
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [this]
    rw [integral_finsetSum _ fun j _ => hint j, ← congrFun hGa k]
    simp only [Matrix.mulVec, dotProduct, momentGram]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]; ring

end RegularityStructures

end
