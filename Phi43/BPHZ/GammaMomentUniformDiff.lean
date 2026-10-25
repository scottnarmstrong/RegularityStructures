/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentUniform
public import Phi43.BPHZ.GammaMomentDiffAll
import Mathlib.Tactic

/-!
# Uniform second moments of the two-scale differences of `v₂`, `v₃`

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the
same white noise, `0 < θ ≤ 1/4`, and all `x, y` (no restriction on `s(y - x)`):

* `gammaWickSq_sub_second_moment_le_uniform`: `E (v₂^ε - v₂^ε')² ≤ C (ε ∨ ε')^(2θ)`;
* `gammaWickCube_sub_second_moment_le_uniform`: `E (v₃^ε - v₃^ε')² ≤ C (ε ∨ ε')^(2θ)`.

As in `Phi43.BPHZ.GammaMomentUniform`, `v(x, y) = T(y) - T(x)` for the kernel tests `T`, applied to
the difference of the Wick-power fields (covariance `≲ (ε ∨ ε')^(2θ) s^(-(n + 2θ))`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- The kernel test of a difference of continuous fields is the difference of the tests. -/
theorem integral_kernelTorus_mul_sub (N : ℕ) (z : SpaceTime) {f g : SpaceTime → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ∫ w, hairerKernelTorus N (z - w) * (f w - g w) =
      (∫ w, hairerKernelTorus N (z - w) * f w) - ∫ w, hairerKernelTorus N (z - w) * g w := by
  rw [← integral_sub (integrable_hairerKernelTorus_sub_mul_continuous N z hf)
    (integrable_hairerKernelTorus_sub_mul_continuous N z hg)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)

/-- The support of the translated kernel lies in a compact time slab. -/
theorem hairerKernelTorus_sub_support (N : ℕ) (z : SpaceTime) :
    ∃ S : Set SpaceTime, IsCompact S ∧ S.Nonempty ∧
      ∀ y, hairerKernelTorus N (z - y) ≠ 0 → y ∈ S := by
  refine ⟨Set.Icc (z.1 - 1) (z.1 + 1) ×ˢ Set.univ, isCompact_Icc.prod isCompact_univ,
    ⟨(z.1, 0), ⟨by linarith, by linarith⟩, Set.mem_univ _⟩, fun y hy => ?_⟩
  refine ⟨?_, Set.mem_univ _⟩
  have h1 : |(z - y).1| ≤ 1 := by
    by_contra hc
    exact hy (hairerKernelTorus_eq_zero_of_one_lt_time N (lt_of_not_ge hc))
  rw [Prod.fst_sub] at h1
  have := abs_le.1 h1
  constructor <;> linarith

/-- Integrability of the square of the kernel test of a difference of Wick squares. -/
theorem integrable_kernelTest_wickSquare_sub_sq (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hW : IsWhiteNoise P W) (hε : 0 < ε) (hε' : 0 < ε')
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (z : SpaceTime) :
    Integrable (fun ω => (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w)) ^ 2) P := by
  obtain ⟨A, -, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} 2 1 le_rfl
  obtain ⟨S, hSc, hS0, hS⟩ := hairerKernelTorus_sub_support N z
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℝ).natDegree ≤ 2 :=
    fun c => by compute_degree
  have h := (hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hSc hS0 (g := fun w => hairerKernelTorus N (z - w))
      ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)) (integrable_hairerKernelTorus_sub N z) hS
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')) (hdeg _) (hdeg _)).1
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  have hc : Continuous (hairerPsiWickSquare N ρ ε ξ ω) :=
    ((continuous_hairerPsiField N hξ.1 ω).pow 2).sub continuous_const
  have hc' : Continuous (hairerPsiWickSquare N ρ' ε' ξ' ω) :=
    ((continuous_hairerPsiField N hξ'.1 ω).pow 2).sub continuous_const
  simp only [integral_kernelTorus_mul_sub N z hc hc']
  have e1 : (∫ y, (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) :
      Polynomial ℝ).eval (hairerPsiField N ξ ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickSquare N ρ ε ξ ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hairerPsiWickSquare, mul_comm])
  have e2 : (∫ y, (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε') :
      Polynomial ℝ).eval (hairerPsiField N ξ' ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickSquare N ρ' ε' ξ' ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hairerPsiWickSquare, mul_comm])
  simp only [e1, e2, mul_one]

/-- Integrability of the square of the kernel test of a difference of Wick cubes. -/
theorem integrable_kernelTest_wickCube_sub_sq (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hW : IsWhiteNoise P W) (hε : 0 < ε) (hε' : 0 < ε')
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (z : SpaceTime) :
    Integrable (fun ω => (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w)) ^ 2) P := by
  obtain ⟨A, -, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} 3 1 le_rfl
  obtain ⟨S, hSc, hS0, hS⟩ := hairerKernelTorus_sub_support N z
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 3 - Polynomial.C (3 * c) * Polynomial.X :
      Polynomial ℝ).natDegree ≤ 3 := fun c => by compute_degree
  have h := (hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hSc hS0 (g := fun w => hairerKernelTorus N (z - w))
      ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)) (integrable_hairerKernelTorus_sub N z) hS
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X)
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X)
    (hdeg _) (hdeg _)).1
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  have hc : Continuous (hairerPsiWickCube N ρ ε ξ ω) :=
    ((continuous_hairerPsiField N hξ.1 ω).pow 3).sub
      (continuous_const.mul (continuous_hairerPsiField N hξ.1 ω))
  have hc' : Continuous (hairerPsiWickCube N ρ' ε' ξ' ω) :=
    ((continuous_hairerPsiField N hξ'.1 ω).pow 3).sub
      (continuous_const.mul (continuous_hairerPsiField N hξ'.1 ω))
  simp only [integral_kernelTorus_mul_sub N z hc hc']
  have e1 : (∫ y, (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) *
      Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickCube N ρ ε ξ ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hairerPsiWickCube, mul_comm])
  have e2 : (∫ y, (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') *
      Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ' ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickCube N ρ' ε' ξ' ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hairerPsiWickCube, mul_comm])
  simp only [e1, e2, mul_one]

end RegularityStructures.Phi43

end
