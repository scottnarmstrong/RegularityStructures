/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldCov

/-!
# Pair integrability of the field of `I(Ψ²) Ψ²`

For fixed `ε > 0` and base point `x`, the field `F(y) = hairerI2Psi2Field N ρ ε ξ x · y` of
[Hai14, (10.39)] satisfies `E F(y)² ≤ M` uniformly in `y` (but not in `ε`), where
`M = (2L)² (24 + 32) c⁴ + (2 L c²)²`, `L = ‖K‖_{L¹}`, `c = hairerWickConstant N ρ ε`.  This follows
from the covariance identity `hairerI2Psi2Field_integral_mul` (chaos `4`, `2`, `0`) and the bound
`|Q_ε| ≤ c` on the covariance.  Consequently `E|F(y) F(ȳ)| ≤ M`, `F(y) ∈ L²`, and `F` is jointly
measurable: these are the hypotheses of the tested second-moment Fubini theorem
`integral_abs_integral_mul_sq_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The kernel `K(y - ·) - K(x - ·)` has `L¹` norm at most `2 ‖K‖_{L¹}`. -/
private theorem integral_abs_kernel_diff_le (N : ℕ) (x y : SpaceTime) :
    ∫ w, |hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)| ≤
      2 * ∫ w, |hairerKernelTorus N w| := by
  have h1 := (integrable_hairerKernelTorus_sub N y).abs
  have h2 := (integrable_hairerKernelTorus_sub N x).abs
  calc ∫ w, |hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)|
      ≤ ∫ w, (|hairerKernelTorus N (y - w)| + |hairerKernelTorus N (x - w)|) :=
        integral_mono (((integrable_hairerKernelTorus_sub N y).sub
          (integrable_hairerKernelTorus_sub N x)).abs) (h1.add h2) fun w => abs_sub _ _
    _ = (∫ w, |hairerKernelTorus N (y - w)|) + ∫ w, |hairerKernelTorus N (x - w)| :=
        integral_add h1 h2
    _ = 2 * ∫ w, |hairerKernelTorus N w| := by
        rw [integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorus N w|) y,
          integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorus N w|) x]
        ring

/-- **Joint measurability of the field of `I(Ψ²) Ψ²`.** -/
theorem measurable_hairerI2Psi2Field_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : SpaceTime) :
    Measurable (fun q : Ω × SpaceTime => hairerI2Psi2Field N ρ ε ξ x q.1 q.2) := by
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hY := measurable_hairerPsiWickSquare_uncurry N hξ
  have h1 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerKernelTorus N (r.1.2 - r.2)) :=
    hK.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have h2 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime => hairerKernelTorus N (x - r.2)) :=
    hK.comp (measurable_const.sub measurable_snd)
  have h3 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerPsiWickSquare N ρ ε ξ r.1.1 r.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ ε ξ q.1 q.2)
      (f := fun r : (Ω × SpaceTime) × SpaceTime => (r.1.1, r.2)) hY
      (measurable_fst.fst.prodMk measurable_snd)
  have hint : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerI2Psi2Kernel N x r.1.2 r.2 * hairerPsiWickSquare N ρ ε ξ r.1.1 r.2) :=
    (h1.sub h2).mul h3
  have hI : Measurable (fun q : Ω × SpaceTime => ∫ w,
      hairerI2Psi2Kernel N x q.2 w * hairerPsiWickSquare N ρ ε ξ q.1 w) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  exact (hI.mul hY).sub_const _

private theorem abs_integral_prod_kernel_le {g g' : SpaceTime → ℝ} {χ : SpaceTime → SpaceTime → ℝ}
    {S : ℝ} (hg : Integrable g) (hg' : Integrable g') (hS : ∀ w w', |χ w w'| ≤ S) :
    |∫ q : SpaceTime × SpaceTime, g q.1 * g' q.2 * χ q.1 q.2| ≤
      (∫ w, |g w|) * (∫ w, |g' w|) * S := by
  have hb : Integrable (fun q : SpaceTime × SpaceTime => |g q.1| * |g' q.2| * S) :=
    (hg.abs.mul_prod hg'.abs).mul_const S
  have h := norm_integral_le_of_norm_le
    (f := fun q : SpaceTime × SpaceTime => g q.1 * g' q.2 * χ q.1 q.2) hb (Filter.Eventually.of_forall fun q => ?_)
  · rw [Real.norm_eq_abs, integral_mul_const] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    exact integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => |g w|) (fun w => |g' w|)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hS _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 :=
  abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩

/-- The mean of the field is bounded by `2 ‖K‖_{L¹} c²`. -/
private theorem abs_mean_hairerI2Psi2_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    |-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2| ≤
      2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2 := by
  have hb := abs_hairerCovariance_le_wickConstant N hρ hε hW hξ
  have hint : Integrable (fun w => |hairerKernelTorus N (x - w)| *
      hairerWickConstant N ρ ε ^ 2) :=
    (integrable_hairerKernelTorus_sub N x).abs.mul_const _
  have h := norm_integral_le_of_norm_le
    (f := fun w => hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2) hint (Filter.Eventually.of_forall fun w => ?_)
  · rw [Real.norm_eq_abs, integral_mul_const,
      integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorus N w|) x] at h
    rw [abs_mul, abs_neg, abs_two]
    linarith
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hb _) 2) (abs_nonneg _)

/-- **Uniform second moment of the field of `I(Ψ²) Ψ²`** (uniform in `y`, not in `ε`). -/
theorem hairerI2Psi2Field_sq_integrable_bound (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    Integrable (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y ^ 2) P ∧
      ∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y ^ 2 ∂P ≤
        (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (24 * hairerWickConstant N ρ ε ^ 4) +
          (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (32 * hairerWickConstant N ρ ε ^ 4) +
          (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) *
            (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) := by
  obtain ⟨hint, heq⟩ := hairerI2Psi2Field_integral_mul N hρ hε hε hW hξ hξ x y y
  simp only [← sq] at hint heq
  refine ⟨hint, heq.trans_le ?_⟩
  have hc : ∀ z, |hairerCrossCovariance N ρ ε ε z| ≤ hairerWickConstant N ρ ε := by
    intro z
    rw [hairerCrossCovariance_self]
    exact abs_hairerCovariance_le_wickConstant N hρ hε hW hξ z
  have hch := fun w w' : SpaceTime => abs_hairerWickSquareFourChaos_le
    (hc (w - y)) (hc (w' - y)) (hc (w - w')) (hc (w - y)) (hc (y - w')) (hc (y - y))
  have hg := integrable_hairerI2Psi2Kernel N x y
  have hL : (∫ w, |hairerI2Psi2Kernel N x y w|) ≤ 2 * ∫ w, |hairerKernelTorus N w| :=
    integral_abs_kernel_diff_le N x y
  have hL0 : 0 ≤ ∫ w, |hairerI2Psi2Kernel N x y w| := integral_nonneg fun _ => abs_nonneg _
  have b4 := abs_integral_prod_kernel_le hg hg
    (χ := fun w w' => hairerI2Psi2Chaos4 N ρ ε ε ε ε y y w w')
    (S := 24 * hairerWickConstant N ρ ε ^ 4) fun w w' => (hch w w').1
  have b2 := abs_integral_prod_kernel_le hg hg
    (χ := fun w w' => hairerI2Psi2Chaos2 N ρ ε ε ε ε y y w w')
    (S := 32 * hairerWickConstant N ρ ε ^ 4) fun w w' => (hch w w').2.1
  have bm := abs_mean_hairerI2Psi2_le N hρ hε hW hξ x y
  have hc4 : 0 ≤ hairerWickConstant N ρ ε ^ 4 := by positivity
  have e4 : (∫ w, |hairerI2Psi2Kernel N x y w|) * (∫ w, |hairerI2Psi2Kernel N x y w|) *
      (24 * hairerWickConstant N ρ ε ^ 4) ≤ (2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|) * (24 * hairerWickConstant N ρ ε ^ 4) := by
    gcongr
  have e2 : (∫ w, |hairerI2Psi2Kernel N x y w|) * (∫ w, |hairerI2Psi2Kernel N x y w|) *
      (32 * hairerWickConstant N ρ ε ^ 4) ≤ (2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|) * (32 * hairerWickConstant N ρ ε ^ 4) := by
    gcongr
  set m := -2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2
  have hmm : m * m ≤ (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) *
      (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) := by
    have := mul_self_le_mul_self (abs_nonneg m) bm
    rwa [abs_mul_abs_self] at this
  have a4 := (le_abs_self _).trans b4
  have a2 := (le_abs_self _).trans b2
  unfold hairerI2Psi2Kernel at *
  linarith

/-- **Pair integrability and a uniform first-moment bound for the field of `I(Ψ²) Ψ²`.** -/
theorem hairerI2Psi2Field_pair_integrable_bound (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : SpaceTime) :
    Integrable (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y') P ∧
      ∫ ω, |hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y'| ∂P ≤
        (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (24 * hairerWickConstant N ρ ε ^ 4) +
          (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (32 * hairerWickConstant N ρ ε ^ 4) +
          (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) *
            (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) := by
  obtain ⟨i1, b1⟩ := hairerI2Psi2Field_sq_integrable_bound N hρ hε hW hξ x y
  obtain ⟨i2, b2⟩ := hairerI2Psi2Field_sq_integrable_bound N hρ hε hW hξ x y'
  have hint := (hairerI2Psi2Field_integral_mul N hρ hε hε hW hξ hξ x y y').1
  refine ⟨hint, ?_⟩
  calc ∫ ω, |hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y'| ∂P
      ≤ ∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y ^ 2 + hairerI2Psi2Field N ρ ε ξ x ω y' ^ 2) / 2
          ∂P := integral_mono hint.abs ((i1.add i2).div_const 2) fun ω => abs_mul_le_half_sq_add _ _
    _ = (∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y ^ 2 ∂P +
          ∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y' ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ _ := by linarith

/-- The field of `I(Ψ²) Ψ²` at a point is square integrable. -/
theorem hairerI2Psi2Field_memLp (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    MemLp (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y) 2 P := by
  have hm : Measurable (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerI2Psi2Field N ρ ε ξ x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerI2Psi2Field_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    (hairerI2Psi2Field_sq_integrable_bound N hρ hε hW hξ x y).1

end RegularityStructures.Phi43

end
