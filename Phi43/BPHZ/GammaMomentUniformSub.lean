/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentUniformDiff
import Mathlib.Tactic

/-!
# Uniform second moments of the two-scale differences of `v₂`, `v₃`

For `0 < θ ≤ 1/4`, `ε, ε' ∈ (0, 1]` and all `x, y` (no restriction on `s(y - x)`),
`E (v₂^ε - v₂^ε')² ≤ C (ε ∨ ε')^(2θ)` and the same for `v₃`
(`gammaWickSq_sub_second_moment_le_uniform`, `gammaWickCube_sub_second_moment_le_uniform`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem flip_le {Rr : SpaceTime → ℝ} {C e : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (h : ∀ x, 0 < torusParabolicSize x → |Rr x| ≤ C * torusParabolicSize x ^ (-e))
    {u v : SpaceTime} (hv : 0 < torusParabolicSize (v - u)) :
    |Rr (u - v)| ≤ (C * 2 ^ e) * torusParabolicSize (v - u) ^ (-e) := by
  have hpos : 0 < torusParabolicSize (u - v) := torusParabolicSize_pos_of_sub_pos hv
  have h1 := h (u - v) hpos
  have hn : -(u - v) = v - u := neg_sub u v
  have h2 := torusParabolicSize_rpow_neg_le_flip he (u := u - v) (by rw [hn]; exact hv)
  rw [hn] at h2
  calc |Rr (u - v)| ≤ C * torusParabolicSize (u - v) ^ (-e) := h1
    _ ≤ C * (2 ^ e * torusParabolicSize (v - u) ^ (-e)) := mul_le_mul_of_nonneg_left h2 hC
    _ = _ := by ring

private theorem sq_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a b : Ω → ℝ} (ha : Integrable (fun ω => a ω ^ 2) P) (hb : Integrable (fun ω => b ω ^ 2) P)
    (hab : Integrable (fun ω => (a ω - b ω) ^ 2) P) :
    ∫ ω, (a ω - b ω) ^ 2 ∂P ≤ 2 * ∫ ω, a ω ^ 2 ∂P + 2 * ∫ ω, b ω ^ 2 ∂P := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (ha.const_mul 2) (hb.const_mul 2)]
  refine integral_mono hab ((ha.const_mul 2).add (hb.const_mul 2)) fun ω => ?_
  simp only
  nlinarith [sq_nonneg (a ω + b ω)]

/-- **Uniform two-scale second moment of `v₂`.** -/
theorem gammaWickSq_sub_second_moment_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime,
        ∫ ω, (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) := by
  obtain ⟨CT, hCT, hT⟩ := kernelTest_second_moment_le N (p := 2 + 2 * θ) (by linarith)
    (by linarith)
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCrossTwo_sq_sub_abs_le N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨A1, -, hA1⟩ := gammaWickSq_sub_integrable_pow_le.{u} 1 le_rfl
  have he : (0 : ℝ) ≤ 2 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (2 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(2 * (2 * (CQ * 2 ^ (2 + 2 * θ)) * CT)) + 2 * (2 * (CQ * 2 ^ (2 + 2 * θ)) * CT),
    by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hCQ h2e)) hCT
      linarith, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickSquare_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hbound : ∀ z : SpaceTime, ∫ ω, (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w)) ^ 2 ∂P ≤
      (2 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ))) * CT := fun z =>
    hT (P := P) (Y := fun ω u => hairerPsiWickSquare N ρ ε ξ ω u - hairerPsiWickSquare N ρ' ε' ξ' ω u)
      ((measurable_hairerPsiWickSquare_uncurry N hξ).sub
        (measurable_hairerPsiWickSquare_uncurry N hξ'))
      (fun u => hairerPsiWickSquare_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
      (M₀ := 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 2 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 2 - hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 2 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 2))
      (fun u => by rw [hcov u u, sub_self])
      (R := fun z => 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 2 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 2 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 2 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 2)) hcov
      (A := 2 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ)))
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCQ hMx) h2e))
      (fun u v hv => by
        have h := flip_le (Rr := fun z => hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 2 -
          hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 2 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 2 +
          hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 2) (C := CQ * (max ε ε') ^ (2 * θ)) he
          (mul_nonneg hCQ hMx) (fun z hz => by
            have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
            rw [show -2 - 2 * θ = -(2 + 2 * θ) by ring] at h0
            exact h0) hv
        rw [abs_mul, abs_two]
        calc 2 * _ ≤ 2 * ((CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ)) *
              torusParabolicSize (v - u) ^ (-(2 + 2 * θ))) :=
              mul_le_mul_of_nonneg_left h (by norm_num)
          _ = _ := by ring) z
  have hint := (hA1 N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y).1
  simp only [mul_one] at hint
  have hw : ∀ z : SpaceTime, ∀ ω, (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w)) =
      (∫ w, hairerKernelTorus N (z - w) * hairerPsiWickSquare N ρ ε ξ ω w) -
        ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickSquare N ρ' ε' ξ' ω w := fun z ω =>
    integral_kernelTorus_mul_sub N z
      (((continuous_hairerPsiField N hξ.1 ω).pow 2).sub continuous_const)
      (((continuous_hairerPsiField N hξ'.1 ω).pow 2).sub continuous_const)
  have hv : ∀ ω, gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω =
      (∫ w, hairerKernelTorus N (y - w) *
        (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w)) -
      ∫ w, hairerKernelTorus N (x - w) *
        (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) := fun ω => by
    rw [hw y ω, hw x ω, gammaWickSq_eq_kernelTest_sub N hξ x y ω,
      gammaWickSq_eq_kernelTest_sub N hξ' x y ω]
    ring
  have key := sq_sub_le
    (integrable_kernelTest_wickSquare_sub_sq N hρ hρ' hW hε.1 hε'.1 hξ hξ' y)
    (integrable_kernelTest_wickSquare_sub_sq N hρ hρ' hW hε.1 hε'.1 hξ hξ' x)
    (by simpa only [hv] using hint)
  simp only [← hv] at key
  have hy := hbound y
  have hx := hbound x
  calc _ ≤ 2 * ∫ ω, (∫ w, hairerKernelTorus N (y - w) * (hairerPsiWickSquare N ρ ε ξ ω w -
          hairerPsiWickSquare N ρ' ε' ξ' ω w)) ^ 2 ∂P + 2 * ∫ ω, (∫ w, hairerKernelTorus N (x - w) *
          (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w)) ^ 2 ∂P := key
    _ ≤ 2 * ((2 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ))) * CT) +
          2 * ((2 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (2 + 2 * θ))) * CT) := by linarith
    _ = _ := by ring

/-- **Uniform two-scale second moment of `v₃`.** -/
theorem gammaWickCube_sub_second_moment_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime,
        ∫ ω, (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) := by
  obtain ⟨CT, hCT, hT⟩ := kernelTest_second_moment_le N (p := 3 + 2 * θ) (by linarith)
    (by linarith)
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCrossTwo_cube_sub_abs_le N ρ ρ' hρ hρ' hθ (θ := θ) (by linarith)
  obtain ⟨A1, -, hA1⟩ := gammaWickCube_sub_integrable_pow_le.{u} 1 le_rfl
  have he : (0 : ℝ) ≤ 3 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (3 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(2 * (6 * (CQ * 2 ^ (3 + 2 * θ)) * CT)) + 2 * (6 * (CQ * 2 ^ (3 + 2 * θ)) * CT),
    by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hCQ h2e)) hCT
      linarith, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickCube_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hbound : ∀ z : SpaceTime, ∫ ω, (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w)) ^ 2 ∂P ≤
      (6 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ))) * CT := fun z =>
    hT (P := P) (Y := fun ω u => hairerPsiWickCube N ρ ε ξ ω u - hairerPsiWickCube N ρ' ε' ξ' ω u)
      ((measurable_hairerPsiWickCube_uncurry N hξ).sub
        (measurable_hairerPsiWickCube_uncurry N hξ'))
      (fun u => hairerPsiWickCube_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
      (M₀ := 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 3 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 3 - hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 3 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 3))
      (fun u => by rw [hcov u u, sub_self])
      (R := fun z => 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 3 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 3 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 3 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 3)) hcov
      (A := 6 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ)))
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCQ hMx) h2e))
      (fun u v hv => by
        have h := flip_le (Rr := fun z => hairerCrossCovarianceTwo N ρ ε ρ ε z ^ 3 -
          hairerCrossCovarianceTwo N ρ ε ρ' ε' z ^ 3 - hairerCrossCovarianceTwo N ρ' ε' ρ ε z ^ 3 +
          hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z ^ 3) (C := CQ * (max ε ε') ^ (2 * θ)) he
          (mul_nonneg hCQ hMx) (fun z hz => by
            have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
            rw [show -3 - 2 * θ = -(3 + 2 * θ) by ring] at h0
            exact h0) hv
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        calc 6 * _ ≤ 6 * ((CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ)) *
              torusParabolicSize (v - u) ^ (-(3 + 2 * θ))) :=
              mul_le_mul_of_nonneg_left h (by norm_num)
          _ = _ := by ring) z
  have hint := (hA1 N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y).1
  simp only [mul_one] at hint
  have hw : ∀ z : SpaceTime, ∀ ω, (∫ w, hairerKernelTorus N (z - w) *
      (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w)) =
      (∫ w, hairerKernelTorus N (z - w) * hairerPsiWickCube N ρ ε ξ ω w) -
        ∫ w, hairerKernelTorus N (z - w) * hairerPsiWickCube N ρ' ε' ξ' ω w := fun z ω =>
    integral_kernelTorus_mul_sub N z
      (((continuous_hairerPsiField N hξ.1 ω).pow 3).sub
        (continuous_const.mul (continuous_hairerPsiField N hξ.1 ω)))
      (((continuous_hairerPsiField N hξ'.1 ω).pow 3).sub
        (continuous_const.mul (continuous_hairerPsiField N hξ'.1 ω)))
  have hv : ∀ ω, gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω =
      (∫ w, hairerKernelTorus N (y - w) *
        (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w)) -
      ∫ w, hairerKernelTorus N (x - w) *
        (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) := fun ω => by
    rw [hw y ω, hw x ω, gammaWickCube_eq_kernelTest_sub N hξ x y ω,
      gammaWickCube_eq_kernelTest_sub N hξ' x y ω]
    ring
  have key := sq_sub_le
    (integrable_kernelTest_wickCube_sub_sq N hρ hρ' hW hε.1 hε'.1 hξ hξ' y)
    (integrable_kernelTest_wickCube_sub_sq N hρ hρ' hW hε.1 hε'.1 hξ hξ' x)
    (by simpa only [hv] using hint)
  simp only [← hv] at key
  have hy := hbound y
  have hx := hbound x
  calc _ ≤ 2 * ∫ ω, (∫ w, hairerKernelTorus N (y - w) * (hairerPsiWickCube N ρ ε ξ ω w -
          hairerPsiWickCube N ρ' ε' ξ' ω w)) ^ 2 ∂P + 2 * ∫ ω, (∫ w, hairerKernelTorus N (x - w) *
          (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w)) ^ 2 ∂P := key
    _ ≤ 2 * ((6 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ))) * CT) +
          2 * ((6 * (CQ * (max ε ε') ^ (2 * θ) * 2 ^ (3 + 2 * θ))) * CT) := by linarith
    _ = _ := by ring

end RegularityStructures.Phi43

end
