/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelTestSecondMoment
public import Phi43.BPHZ.GammaMomentLp
import Mathlib.Tactic

/-!
# Uniform second moments of `v₂` and `v₃`

`v₂(x, y) = ∫ δK_{x,y} :Ψ²:` and `v₃(x, y) = ∫ δK_{x,y} :Ψ³:` are differences `T(y) - T(x)` of the
kernel tests `T(z) = ∫ K(z - w) :Ψⁿ:(w) dw` (pathwise, since both integrands are integrable).
Each test has second moment bounded uniformly in `z` (`kernelTest_second_moment_le`), hence

`E v₂(x, y)² ≤ C`, `E v₃(x, y)² ≤ C` for all `x, y`, `ε ∈ (0, 1]`

(`gammaWickSq_second_moment_le_uniform`, `gammaWickCube_second_moment_le_uniform`).  These replace the
restriction `s(y - x) ≤ 1` of `gammaWickSq_second_moment_le`, `gammaWickCube_second_moment_le` for the
large distances required by the global quantifier over `x, y` of the Kolmogorov bound for the
model norms.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem integral_sq_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b : Ω → ℝ}
    (ha : Integrable (fun ω => a ω ^ 2) P) (hb : Integrable (fun ω => b ω ^ 2) P)
    (hab : Integrable (fun ω => (a ω - b ω) ^ 2) P) :
    ∫ ω, (a ω - b ω) ^ 2 ∂P ≤ 2 * ∫ ω, a ω ^ 2 ∂P + 2 * ∫ ω, b ω ^ 2 ∂P := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (ha.const_mul 2) (hb.const_mul 2)]
  refine integral_mono hab ((ha.const_mul 2).add (hb.const_mul 2)) fun ω => ?_
  simp only
  nlinarith [sq_nonneg (a ω + b ω)]

private theorem abs_cov_sq_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u v : SpaceTime}
    (h : 0 < torusParabolicSize (v - u)) :
    |2 * Q (u - v) ^ 2| ≤ (8 * B ^ 2) * torusParabolicSize (v - u) ^ (-(2 : ℝ)) := by
  have h1 := sq_cov_flip_le hB hQ h
  rw [abs_of_nonneg (by positivity)]
  linarith

private theorem abs_cov_cube_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u v : SpaceTime}
    (h : 0 < torusParabolicSize (v - u)) :
    |6 * Q (u - v) ^ 3| ≤ (48 * B ^ 3) * torusParabolicSize (v - u) ^ (-(3 : ℝ)) := by
  have h1 := abs_cov_flip_le hB hQ h
  have h3 : (torusParabolicSize (v - u) ^ (-(1 : ℝ))) ^ 3 =
      torusParabolicSize (v - u) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
    norm_num
  have h0 : 0 ≤ |Q (u - v)| := abs_nonneg _
  have h2 : |Q (u - v)| ^ 3 ≤ (2 * B * torusParabolicSize (v - u) ^ (-(1 : ℝ))) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  rw [mul_pow, h3] at h2
  rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  nlinarith [Real.rpow_nonneg h.le (-(3 : ℝ))]

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The pathwise decomposition `v₂(x, y) = T(y) - T(x)`. -/
theorem gammaWickSq_eq_kernelTest_sub (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x y : SpaceTime) (ω : Ω) :
    gammaWickSq N ρ ε ξ x y ω = (∫ w, hairerKernelTorus N (y - w) * hairerPsiWickSquare N ρ ε ξ ω w) -
      ∫ w, hairerKernelTorus N (x - w) * hairerPsiWickSquare N ρ ε ξ ω w := by
  have hc : Continuous (hairerPsiWickSquare N ρ ε ξ ω) :=
    ((continuous_hairerPsiField N hξ.1 ω).pow 2).sub continuous_const
  rw [← integral_sub (integrable_hairerKernelTorus_sub_mul_continuous N y hc)
    (integrable_hairerKernelTorus_sub_mul_continuous N x hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hairerI2Psi2Kernel]
  ring

/-- The pathwise decomposition `v₃(x, y) = T(y) - T(x)`. -/
theorem gammaWickCube_eq_kernelTest_sub (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x y : SpaceTime) (ω : Ω) :
    gammaWickCube N ρ ε ξ x y ω = (∫ w, hairerKernelTorus N (y - w) * hairerPsiWickCube N ρ ε ξ ω w) -
      ∫ w, hairerKernelTorus N (x - w) * hairerPsiWickCube N ρ ε ξ ω w := by
  have hc : Continuous (hairerPsiWickCube N ρ ε ξ ω) :=
    ((continuous_hairerPsiField N hξ.1 ω).pow 3).sub
      (continuous_const.mul (continuous_hairerPsiField N hξ.1 ω))
  rw [← integral_sub (integrable_hairerKernelTorus_sub_mul_continuous N y hc)
    (integrable_hairerKernelTorus_sub_mul_continuous N x hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hairerI2Psi2Kernel]
  ring

/-- Integrability of the square of the kernel test of the Wick square. -/
theorem integrable_kernelTest_wickSquare_sq (N : ℕ) (hρ : IsMollifier ρ) (hW : IsWhiteNoise P W)
    (hε : 0 < ε) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    Integrable (fun ω => (∫ w, hairerKernelTorus N (z - w) *
      hairerPsiWickSquare N ρ ε ξ ω w) ^ 2) P := by
  obtain ⟨A, -, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u}
    2 1 le_rfl
  set Q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hQ
  have hdeg : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := (hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (g := fun w => hairerKernelTorus N (z - w))
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)) (integrable_hairerKernelTorus_sub N z) Q hdeg).1
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  have e : (∫ y, Q.eval (hairerPsiField N ξ ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickSquare N ρ ε ξ ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hQ, hairerPsiWickSquare, mul_comm])
  simp only [e]

/-- Integrability of the square of the kernel test of the Wick cube. -/
theorem integrable_kernelTest_wickCube_sq (N : ℕ) (hρ : IsMollifier ρ) (hW : IsWhiteNoise P W)
    (hε : 0 < ε) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    Integrable (fun ω => (∫ w, hairerKernelTorus N (z - w) *
      hairerPsiWickCube N ρ ε ξ ω w) ^ 2) P := by
  obtain ⟨A, -, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u}
    3 1 le_rfl
  set Q : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hQ
  have hdeg : Q.natDegree ≤ 3 := by rw [hQ]; compute_degree
  have h := (hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (g := fun w => hairerKernelTorus N (z - w))
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)) (integrable_hairerKernelTorus_sub N z) Q hdeg).1
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  have e : (∫ y, Q.eval (hairerPsiField N ξ ω y) * hairerKernelTorus N (z - y)) =
      ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickCube N ρ ε ξ ω w :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [hQ, hairerPsiWickCube, mul_comm])
  simp only [e]

/-- **Uniform second moment of `v₂`**: `E v₂(x, y)² ≤ C` for all `x, y` and `ε ∈ (0, 1]`. -/
theorem gammaWickSq_second_moment_le_uniform (N : ℕ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, ∫ ω, gammaWickSq N ρ ε ξ x y ω ^ 2 ∂P ≤ C := by
  obtain ⟨CT, hCT, hT⟩ := kernelTest_second_moment_le N (p := 2) le_rfl (by norm_num)
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨A1, -, hA1⟩ := gammaWickSq_integrable_pow_le.{u} 1 le_rfl
  refine ⟨2 * (8 * BQ ^ 2 * CT) + 2 * (8 * BQ ^ 2 * CT), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ
  have hbound : ∀ z : SpaceTime, ∫ ω, (∫ w, hairerKernelTorus N (z - w) *
      hairerPsiWickSquare N ρ ε ξ ω w) ^ 2 ∂P ≤ 8 * BQ ^ 2 * CT := fun z =>
    hT (P := P) (Y := hairerPsiWickSquare N ρ ε ξ) (measurable_hairerPsiWickSquare_uncurry N hξ)
      (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u)
      (M₀ := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by rw [hcov u u, sub_self])
      (R := fun z => 2 * hairerCovariance N ρ ε z ^ 2) hcov (A := 8 * BQ ^ 2) (by positivity)
      (fun u v h => abs_cov_sq_le hBQ (hQ hε.1 hε.2) h) z
  have hint := (hA1 N hρ hW hε.1 hξ x y).1
  simp only [mul_one] at hint
  have key := integral_sq_sub_le (integrable_kernelTest_wickSquare_sq N hρ hW hε.1 hξ y)
    (integrable_kernelTest_wickSquare_sq N hρ hW hε.1 hξ x)
    (by simpa only [gammaWickSq_eq_kernelTest_sub N hξ x y] using hint)
  simp only [← gammaWickSq_eq_kernelTest_sub N hξ x y] at key
  have := hbound y
  have := hbound x
  linarith

/-- **Uniform second moment of `v₃`**: `E v₃(x, y)² ≤ C` for all `x, y` and `ε ∈ (0, 1]`. -/
theorem gammaWickCube_second_moment_le_uniform (N : ℕ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, ∫ ω, gammaWickCube N ρ ε ξ x y ω ^ 2 ∂P ≤ C := by
  obtain ⟨CT, hCT, hT⟩ := kernelTest_second_moment_le N (p := 3) (by norm_num) (by norm_num)
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨A1, -, hA1⟩ := gammaWickCube_integrable_pow_le.{u} 1 le_rfl
  refine ⟨2 * (48 * BQ ^ 3 * CT) + 2 * (48 * BQ ^ 3 * CT), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiWickCube_integral_mul N hρ hε.1 hW hξ
  have hbound : ∀ z : SpaceTime, ∫ ω, (∫ w, hairerKernelTorus N (z - w) *
      hairerPsiWickCube N ρ ε ξ ω w) ^ 2 ∂P ≤ 48 * BQ ^ 3 * CT := fun z =>
    hT (P := P) (Y := hairerPsiWickCube N ρ ε ξ) (measurable_hairerPsiWickCube_uncurry N hξ)
      (fun u => hairerPsiWickCube_memLp N hρ hε.1 hW hξ u)
      (M₀ := 6 * hairerCovariance N ρ ε 0 ^ 3) (fun u => by rw [hcov u u, sub_self])
      (R := fun z => 6 * hairerCovariance N ρ ε z ^ 3) hcov (A := 48 * BQ ^ 3) (by positivity)
      (fun u v h => abs_cov_cube_le hBQ (hQ hε.1 hε.2) h) z
  have hint := (hA1 N hρ hW hε.1 hξ x y).1
  simp only [mul_one] at hint
  have key := integral_sq_sub_le (integrable_kernelTest_wickCube_sq N hρ hW hε.1 hξ y)
    (integrable_kernelTest_wickCube_sq N hρ hW hε.1 hξ x)
    (by simpa only [gammaWickCube_eq_kernelTest_sub N hξ x y] using hint)
  simp only [← gammaWickCube_eq_kernelTest_sub N hξ x y] at key
  have := hbound y
  have := hbound x
  linarith

end RegularityStructures.Phi43

end
