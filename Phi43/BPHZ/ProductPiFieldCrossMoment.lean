/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldCross
public import Phi43.BPHZ.ProductPiFieldMoment

/-!
# Two-scale, two-mollifier pair integrability for `I₂Ψ`

For mollifiers `ρ, ρ'`, scales `ε, ε' > 0`, noises `ξ, ξ'` of the same white noise, a base point `x`
and points `y, ȳ`, the product `I₂Ψ_{ρ,ε}(y) I₂Ψ_{ρ',ε'}(ȳ)` is integrable on `Ω` with first moment
bounded uniformly in `y, ȳ` (`productISqPsiField_two_scale_pair_integrable_cross`), and the kernel
of the two-scale covariance identity is integrable (`productISqPsiField_two_scale_kernel_integrable_cross`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Two-scale pair integrability and a first-moment bound for `I₂Ψ`.** -/
theorem productISqPsiField_two_scale_pair_integrable_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x y y' : SpaceTime) :
    Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y') P ∧
      ∫ ω, |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| ∂P ≤
        10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3 *
          ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|)) := by
  have := hW.isProbabilityMeasure
  set g : SpaceTime → SpaceTime → ℝ := fun z w =>
    hairerKernelTorus N (z - w) - hairerKernelTorus N (x - w) with hgdef
  have hg : ∀ z, Integrable (g z) := fun z =>
    (integrable_hairerKernelTorus_sub N z).sub (integrable_hairerKernelTorus_sub N x)
  have hdata := fun q : SpaceTime × SpaceTime =>
    hairerPsiWickSquare_pair_data_cross N hρ hρ' hε hε' hW hξ hξ' q.1 y q.2 y'
  have hY := measurable_hairerPsiWickSquare_uncurry N hξ
  have hY' := measurable_hairerPsiWickSquare_uncurry N hξ'
  have ha := measurable_hairerPsiField_apply N hξ y
  have hb := measurable_hairerPsiField_apply N hξ' y'
  have hi := fun q : SpaceTime × SpaceTime => (hdata q).1
  have hM := fun q : SpaceTime × SpaceTime => (hdata q).2.1
  have hF := integrable_testedPair_integrand hY hY' ha hb (hg y) (hg y') hi hM
  set G : Ω → SpaceTime × SpaceTime → ℝ := fun ω q => (g y q.1 * g y' q.2) *
    (hairerPsiWickSquare N ρ ε ξ ω q.1 * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ' ε' ξ' ω q.2 * hairerPsiField N ξ' ω y')) with hGdef
  have hsq : ∀ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' =
      ∫ q : SpaceTime × SpaceTime, G ω q := by
    intro ω
    have h := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => g y w * hairerPsiWickSquare N ρ ε ξ ω w)
      (fun w => g y' w * hairerPsiWickSquare N ρ' ε' ξ' ω w)
    have h2 : ∫ q : SpaceTime × SpaceTime, G ω q =
        (∫ q : SpaceTime × SpaceTime, (g y q.1 * hairerPsiWickSquare N ρ ε ξ ω q.1) *
          (g y' q.2 * hairerPsiWickSquare N ρ' ε' ξ' ω q.2)) *
          (hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y') := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => by simp only [hGdef]; ring)
    rw [h2, show (∫ q : SpaceTime × SpaceTime, (g y q.1 * hairerPsiWickSquare N ρ ε ξ ω q.1) *
      (g y' q.2 * hairerPsiWickSquare N ρ' ε' ξ' ω q.2)) =
        (∫ w, g y w * hairerPsiWickSquare N ρ ε ξ ω w) *
          ∫ w, g y' w * hairerPsiWickSquare N ρ' ε' ξ' ω w from h]
    simp only [productISqPsiField, hgdef, hairerI2Psi2Kernel]
    ring
  have hFint : Integrable (fun ω => ∫ q : SpaceTime × SpaceTime, G ω q) P :=
    hF.integral_prod_left
  refine ⟨hFint.congr (Filter.Eventually.of_forall fun ω => (hsq ω).symm), ?_⟩
  have hFn : Integrable (fun ω => ∫ q : SpaceTime × SpaceTime, ‖G ω q‖) P :=
    hF.norm.integral_prod_left
  have hswap := integral_integral_swap (f := fun ω q => ‖G ω q‖) hF.norm
  calc ∫ ω, |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| ∂P
      ≤ ∫ ω, (∫ q : SpaceTime × SpaceTime, ‖G ω q‖) ∂P := by
        refine integral_mono (hFint.congr (Filter.Eventually.of_forall fun ω => (hsq ω).symm)).abs
          hFn fun ω => ?_
        rw [hsq ω]
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (G ω)
    _ = ∫ q : SpaceTime × SpaceTime, ∫ ω, ‖G ω q‖ ∂P := hswap
    _ ≤ ∫ q : SpaceTime × SpaceTime, |g y q.1| * |g y' q.2| *
          (10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun q => integral_nonneg fun ω => norm_nonneg _) ?_
          (Filter.Eventually.of_forall fun q => ?_)
        · exact ((hg y).abs.mul_prod (hg y').abs).mul_const _
        · have e : ∫ ω, ‖G ω q‖ ∂P = |g y q.1| * |g y' q.2| * ∫ ω,
              |hairerPsiWickSquare N ρ ε ξ ω q.1 * hairerPsiField N ξ ω y *
                (hairerPsiWickSquare N ρ' ε' ξ' ω q.2 * hairerPsiField N ξ' ω y')| ∂P := by
            rw [← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            simp only [hGdef, Real.norm_eq_abs]
            rw [abs_mul (g y q.1 * g y' q.2), abs_mul (g y q.1)]
          beta_reduce
          rw [e]
          exact mul_le_mul_of_nonneg_left (hM q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∫ w, |g y w|) * (∫ w, |g y' w|) *
          (10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3) := by
        rw [integral_mul_const]
        congr 1
        exact integral_prod_mul (fun w => |g y w|) (fun w => |g y' w|)
    _ ≤ ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|)) *
          (10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3) := by
        have h0 : 0 ≤ 10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3 :=
          mul_nonneg (by norm_num) (pow_nonneg (le_max_of_le_left (productWickConstant_nonneg N ρ ε)) 3)
        have hL : 0 ≤ ∫ w, |hairerKernelTorus N w| :=
          integral_nonneg fun w => abs_nonneg (hairerKernelTorus N w)
        refine mul_le_mul_of_nonneg_right ?_ h0
        exact mul_le_mul (integral_abs_hairerKernelTorus_diff_le N x y)
          (integral_abs_hairerKernelTorus_diff_le N x y') (integral_nonneg fun _ => abs_nonneg _)
          (by linarith)
    _ = _ := mul_comm _ _

/-- **Integrability of the two-scale covariance kernel.** -/
theorem productISqPsiField_two_scale_kernel_integrable_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x x' y y' : SpaceTime) :
    Integrable (Function.uncurry fun w w' =>
      hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x' y' w' *
        isqBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovarianceTwo N ρ ε ρ' ε')
          (hairerCovariance N ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
          (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε') w y w' y')
      (volume.prod volume) := by
  have := hW.isProbabilityMeasure
  set g : SpaceTime → ℝ := fun w => hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)
    with hgdef
  set g' : SpaceTime → ℝ := fun w => hairerKernelTorus N (y' - w) - hairerKernelTorus N (x' - w)
    with hg'def
  have hg : Integrable g :=
    (integrable_hairerKernelTorus_sub N y).sub (integrable_hairerKernelTorus_sub N x)
  have hg' : Integrable g' :=
    (integrable_hairerKernelTorus_sub N y').sub (integrable_hairerKernelTorus_sub N x')
  have hdata := fun q : SpaceTime × SpaceTime =>
    hairerPsiWickSquare_pair_data_cross N hρ hρ' hε hε' hW hξ hξ' q.1 y q.2 y'
  have hY := measurable_hairerPsiWickSquare_uncurry N hξ
  have hY' := measurable_hairerPsiWickSquare_uncurry N hξ'
  have ha := measurable_hairerPsiField_apply N hξ y
  have hb := measurable_hairerPsiField_apply N hξ' y'
  have hi := fun q : SpaceTime × SpaceTime => (hdata q).1
  have hM := fun q : SpaceTime × SpaceTime => (hdata q).2.1
  have hexp := integrable_testedPair_expectation hY hY' ha hb hg hg' hi hM
  refine hexp.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.uncurry, (hdata q).2.2]
  rfl

end RegularityStructures.Phi43

end
