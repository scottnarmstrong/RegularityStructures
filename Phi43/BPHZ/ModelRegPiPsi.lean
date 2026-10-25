/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiAllMoments
public import Phi43.BPHZ.ModelRegPiMoment
public import Phi43.BPHZ.ModelRegPiRandom
public import Phi43.BPHZ.SemigroupTestAllMoments

/-!
# The `q`-th moment of `Q_t Π_x Ψ (x)` for the random models

For `τ = Ψ` the ingredients of the Kolmogorov criterion hold for the random models:
almost surely `Q_t(x, ·) Ψ_ε(proj ·)` is integrable (`hairerPsiField_kernel_integrable_ae`), the
tested field `⟨Ψ_ε, q^♯_t(x, ·)⟩` has all moments equivalent to its second moment, with
integrability (`hairerPsiField_semigroupPeriodised_integrable_pow_le`), and combining with the
random corollary `ae_regPi_single_psi_eq` and the second moment bound of `SemigroupTestPsi`
gives, for `t ∈ (0, 1]`, `ε ∈ (0, 1]` and `κ̄ ≤ κ`,

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single Ψ 1) t x‖ₑ ^ q ≤ ofReal (C * t ^ ((deg Ψ + κ̄) / 4)) ^ q`

(`regPi_psi_lintegral_enorm_pow_le`), with `C` independent of `ε`, `t`, `x`, the noise and `Z`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- Almost surely the kernel `Q_t(x, ·)` times the lifted field `Ψ_ε ∘ proj` is integrable on
`ℝ⁴`. -/
theorem hairerPsiField_kernel_integrable_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      hairerPsiField N ξ ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiField_integral_mul N hρ hε hW hξ
  have hYm : Measurable (fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2) :=
    measurable_hairerPsiField_uncurry N hξ
  have hK : Integrable (fun y => parabolicSemigroup.kernel t x y) :=
    integrable_parabolicKernel_sub ht x
  have hYj : AEStronglyMeasurable (Function.uncurry fun (ω : Ω) (y : ParabolicSpace) =>
      hairerPsiField N ξ ω (spaceTimeProj y)) (P.prod volume) :=
    (hYm.comp (measurable_fst.prodMk
      (continuous_spaceTimeProj.measurable.comp measurable_snd))).aestronglyMeasurable
  have hYi : ∀ y : ParabolicSpace,
      Integrable (fun ω => hairerPsiField N ξ ω (spaceTimeProj y)) P :=
    fun y => (hairerPsiField_memLp N hρ hε hW hξ (spaceTimeProj y)).integrable one_le_two
  have hM : ∀ y : ParabolicSpace, ∫ ω, |hairerPsiField N ξ ω (spaceTimeProj y)| ∂P ≤
      (hairerCovariance N ρ ε 0 + 1) / 2 := by
    intro y
    have hsq : Integrable (fun ω => hairerPsiField N ξ ω (spaceTimeProj y) *
        hairerPsiField N ξ ω (spaceTimeProj y)) P :=
      (hairerPsiField_memLp N hρ hε hW hξ _).integrable_mul
        (hairerPsiField_memLp N hρ hε hW hξ _)
    calc ∫ ω, |hairerPsiField N ξ ω (spaceTimeProj y)| ∂P
        ≤ ∫ ω, (hairerPsiField N ξ ω (spaceTimeProj y) *
            hairerPsiField N ξ ω (spaceTimeProj y) + 1) / 2 ∂P := by
          refine integral_mono (hYi y).abs ((hsq.add (integrable_const 1)).div_const 2)
            fun ω => ?_
          nlinarith [sq_nonneg (|hairerPsiField N ξ ω (spaceTimeProj y)| - 1),
            abs_mul_abs_self (hairerPsiField N ξ ω (spaceTimeProj y))]
      _ = (hairerCovariance N ρ ε 0 + 1) / 2 := by
          rw [integral_div, integral_add hsq (integrable_const 1), hcov, sub_self]
          simp
  exact (integrable_uncurry_mul_of_bound hK hYj hYi hM).prod_right_ae

/-- **All moments of the tested `Ψ`, with integrability.**  The tested field
`⟨Ψ_ε, q^♯_t(z, ·)⟩` has integrable `2p`-th power and
`E X^(2p) ≤ A (E X²)^p`, with `A = A(p)`. -/
theorem hairerPsiField_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, hairerPsiField N ξ ω w * semigroupPeriodised t z w) ^ (2 * p))
          P ∧
        ∫ ω, (∫ w, hairerPsiField N ξ ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerPsiField N ξ ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Polynomial.X (by simp)
  simpa only [Polynomial.eval_X] using h

end RegularityStructures.Phi43

end
