/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
public import RegularityStructures.Analysis.Parabolic.TestFunction
public import RegularityStructures.Abstract.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Bumps with prescribed polynomial moments

For a smooth nonnegative `χ` supported in the unit parabolic ball and positive on a nonempty open
set, the Gram matrix `G k j = ∫ z^k z^j χ` of the monomials `z^k`, `|k|_𝔰 < N`, is invertible
(`isUnit_det_momentGram`). Consequently any prescribed moments are attained by a smooth bump
supported in the unit ball (`exists_moment_bump`), as used in the proof of [Hai14, Lemma 5.5].

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.5.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The monomial function `z ↦ z^k` on parabolic space. -/
def momentMono (k : Fin 4 →₀ ℕ) (z : ParabolicSpace) : ℝ :=
  evalParabolic (MvPolynomial.monomial k 1) z

/-- The Gram matrix `G k j = ∫ z^k z^j χ(z) dz` of the monomials of parabolic degree `< N`. -/
def momentGram (N : ℕ) (χ : ParabolicSpace → ℝ) : Matrix (PolyIndex N) (PolyIndex N) ℝ :=
  fun k j => ∫ z, momentMono k.1 z * momentMono j.1 z * χ z

end RegularityStructures

end

public section

namespace RegularityStructures

open MeasureTheory Matrix

/-- The inverse of the coordinate map `parabolicCoords`. -/
theorem parabolicCoords_surj (x : Fin 4 → ℝ) :
    parabolicCoords (x 0, ![x 1, x 2, x 3]) = x := by
  funext i
  fin_cases i <;> simp [parabolicCoords]

/-- A polynomial vanishing on a nonempty open subset of parabolic space is zero. -/
theorem eq_zero_of_evalParabolic_eq_zero_on_open {p : MvPolynomial (Fin 4) ℝ}
    {U : Set ParabolicSpace} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ z ∈ U, evalParabolic p z = 0) : p = 0 := by
  obtain ⟨z0, hz0⟩ := hne
  set e : (Fin 4 → ℝ) → ParabolicSpace := fun x => (x 0, ![x 1, x 2, x 3]) with he
  have hec : Continuous e := by
    refine (continuous_apply 0).prodMk (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hV : IsOpen (e ⁻¹' U) := hU.preimage hec
  have hmem : parabolicCoords z0 ∈ e ⁻¹' U := by
    have : e (parabolicCoords z0) = z0 := by
      simp only [he, parabolicCoords]
      ext i <;> [rfl; fin_cases i <;> rfl]
    simpa [this] using hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ hmem
  refine MvPolynomial.funext_set (fun i => Set.Ioo (parabolicCoords z0 i - ε / 2)
    (parabolicCoords z0 i + ε / 2)) (fun _ => Set.Ioo_infinite (by linarith)) (q := 0) ?_
  intro x hx
  have hx' : x ∈ Metric.ball (parabolicCoords z0) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have := hx i (Set.mem_univ i)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [this.1, this.2]
  have := h (e x) (hball hx')
  unfold evalParabolic at this
  rw [parabolicCoords_surj x] at this
  simpa using this

open scoped ContDiff in
theorem contDiff_parabolicCoords (i : Fin 4) : ContDiff ℝ ∞ fun z : ParabolicSpace =>
    parabolicCoords z i := by
  fin_cases i
  · exact contDiff_fst
  · exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  · exact (contDiff_apply ℝ ℝ 1).comp contDiff_snd
  · exact (contDiff_apply ℝ ℝ 2).comp contDiff_snd

open scoped ContDiff in
theorem contDiff_evalParabolic (p : MvPolynomial (Fin 4) ℝ) :
    ContDiff ℝ ∞ (evalParabolic p) := by
  unfold evalParabolic
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_parabolicCoords i)

open scoped ContDiff in
theorem contDiff_momentMono (k : Fin 4 →₀ ℕ) : ContDiff ℝ ∞ (momentMono k) :=
  contDiff_evalParabolic _

open scoped ContDiff in
theorem integrable_momentMono_mul_mul {χ : ParabolicSpace → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : ∀ z, 1 < parabolicNorm z → χ z = 0) (k j : Fin 4 →₀ ℕ) :
    Integrable fun z => momentMono k z * momentMono j z * χ z := by
  refine integrable_of_continuous_unit
    (((contDiff_momentMono k).mul (contDiff_momentMono j)).mul hχ).continuous fun z hz => ?_
  simp [hsupp z hz]

theorem evalParabolic_toPoly {N : ℕ} (v : PolyIndex N → ℝ) (z : ParabolicSpace) :
    evalParabolic (toPoly N v) z = ∑ k, v k * momentMono k.1 z := by
  simp [toPoly_apply, evalParabolic, momentMono, map_sum]

open scoped ContDiff in
/-- The quadratic form of the Gram matrix is `∫ (∑ v_k z^k)² χ`. -/
theorem dotProduct_momentGram_mulVec {N : ℕ} {χ : ParabolicSpace → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : ∀ z, 1 < parabolicNorm z → χ z = 0) (v : PolyIndex N → ℝ) :
    v ⬝ᵥ (momentGram N χ *ᵥ v) = ∫ z, (evalParabolic (toPoly N v) z) ^ 2 * χ z := by
  have hint : ∀ k j : PolyIndex N, Integrable fun z => v k * (v j * (momentMono k.1 z * momentMono j.1 z *
      χ z)) := fun k j => ((integrable_momentMono_mul_mul hχ hsupp k.1 j.1).const_mul (v j)).const_mul
        (v k)
  have : ∀ z, (evalParabolic (toPoly N v) z) ^ 2 * χ z =
      ∑ k, ∑ j, v k * (v j * (momentMono k.1 z * momentMono j.1 z * χ z)) := fun z => by
    rw [evalParabolic_toPoly, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [this]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j]
  simp only [dotProduct, Matrix.mulVec, momentGram]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => hint k j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul]; ring

open scoped ContDiff in
/-- The Gram matrix of the monomials against a bump `χ ≥ 0` that is positive on a nonempty open
set is invertible: its quadratic form is `∫ (∑ v_k z^k)² χ > 0` for `v ≠ 0`. -/
theorem isUnit_det_momentGram {N : ℕ} {χ : ParabolicSpace → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hnn : ∀ z, 0 ≤ χ z) (hsupp : ∀ z, 1 < parabolicNorm z → χ z = 0)
    (hpos : ∃ U : Set ParabolicSpace, IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, 0 < χ z) :
    IsUnit (momentGram N χ).det := by
  obtain ⟨U, hU, hUne, hUpos⟩ := hpos
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ u : PolyIndex N → ℝ, momentGram N χ *ᵥ u = 0 → u = 0 := by
    intro u hu
    by_contra hu0
    have hq : toPoly N u ≠ 0 := fun h => hu0 (by simpa [h] using (ofPoly_toPoly u).symm)
    obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, evalParabolic (toPoly N u) z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq (eq_zero_of_evalParabolic_eq_zero_on_open hU hUne hcon)
    have hform := dotProduct_momentGram_mulVec hχ hsupp u
    rw [hu, dotProduct_zero] at hform
    have hc : Continuous fun z => (evalParabolic (toPoly N u) z) ^ 2 * χ z :=
      ((contDiff_evalParabolic _).continuous.pow 2).mul hχ.continuous
    have hcs : HasCompactSupport fun z => (evalParabolic (toPoly N u) z) ^ 2 * χ z :=
      hasCompactSupport_of_eq_zero_unit fun z hz1 => by simp [hsupp z hz1]
    have hpos' := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure ParabolicSpace)) hcs
      (fun z => mul_nonneg (sq_nonneg _) (hnn z)) (x := z)
      (mul_ne_zero (pow_ne_zero 2 hz) (hUpos z hzU).ne')
    linarith
  intro v w hvw
  rw [← sub_eq_zero]
  exact key _ (by rw [Matrix.mulVec_sub, hvw, sub_self])

end RegularityStructures

end
