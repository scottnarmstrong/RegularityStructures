/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossSub
public import Phi43.BPHZ.TreeI2Psi2CrossPointwise
public import Phi43.BPHZ.TreeI2Psi2DifferenceCov

/-!
# The covariance of the cross-mollifier difference of `I(Ψ²) Ψ²`, split by chaos

`hairerI2Psi2Cov_sub_cross`: for mollifiers `ρ, ρ'`, scales `a, b > 0` and noises `ξ, ξ'` of the
same white noise,
`Cov(ρa,ρa) - Cov(ρa,ρ'b) - Cov(ρ'b,ρa) + Cov(ρ'b,ρ'b) = ∫∫ δK_y δK_y' Δ₄ + ∫∫ δK_y δK_y' Δ₂ +
(m_{ρ,a}(y) - m_{ρ',b}(y)) (m_{ρ,a}(y') - m_{ρ',b}(y'))`
where `Δ₄`, `Δ₂` are the second differences of the chaos kernels
(`i2Psi2DiffChaos4Two`, `i2Psi2DiffChaos2Two`) and `m_{ρ,s}` is the mean of the field (`i2Psi2Mean`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

private theorem integral_comb4_cross {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ : α → ℝ} (i₁ : Integrable f₁ μ) (i₂ : Integrable f₂ μ) (i₃ : Integrable f₃ μ)
    (i₄ : Integrable f₄ μ) :
    ∫ a, (f₁ a - f₂ a - f₃ a + f₄ a) ∂μ =
      (∫ a, f₁ a ∂μ) - (∫ a, f₂ a ∂μ) - (∫ a, f₃ a ∂μ) + ∫ a, f₄ a ∂μ := by
  have j2 : Integrable (fun a => f₁ a - f₂ a) μ := i₁.sub i₂
  have j3 : Integrable (fun a => f₁ a - f₂ a - f₃ a) μ := j2.sub i₃
  rw [integral_add j3 i₄, integral_sub j2 i₃, integral_sub i₁ i₂]

/-- The chaos-`4` and chaos-`2` integrals at scales `(s, t)` are integrable. -/
theorem integrable_hairerI2Psi2_chaos_two_mollifier (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ s ξ)
    (hξ' : IsRegularisedNoise P W ρ' t ξ') (x y y' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => hairerI2Psi2Kernel N x y q.1 *
      hairerI2Psi2Kernel N x y' q.2 * hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![s, s, t, t] y y' q.1 q.2) ∧
    Integrable (fun q : SpaceTime × SpaceTime => hairerI2Psi2Kernel N x y q.1 *
      hairerI2Psi2Kernel N x y' q.2 * hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![s, s, t, t] y y' q.1 q.2) := by
  have hε : ∀ i : Fin 4, 0 < (![s, s, t, t] : Fin 4 → ℝ) i := by
    intro i; fin_cases i <;> simpa using (by assumption)
  have hρ4 : ∀ i : Fin 4, IsMollifier ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i) := by
    intro i; fin_cases i <;> simpa using (by assumption)
  have hξ4 : ∀ i : Fin 4, IsRegularisedNoise P W
      ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i) ((![s, s, t, t] : Fin 4 → ℝ) i)
      ((![ξ, ξ, ξ', ξ'] : Fin 4 → Ω → SpaceTime → ℝ) i) := by
    intro i; fin_cases i <;> simpa using (by assumption)
  obtain ⟨h4, h2, -⟩ := integrable_hairerI2Psi2ChaosTwo N hρ4 hε hW hξ4
    (integrable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y') y y'
  exact ⟨h4, h2⟩

/-- **The covariance of the two-scale difference, split by chaos.** -/
theorem hairerI2Psi2Cov_sub_cross (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ a ξ)
    (hξ' : IsRegularisedNoise P W ρ' b ξ') (x y y' : SpaceTime) :
    hairerI2Psi2CovTwo N ρ ρ x a a y y' - hairerI2Psi2CovTwo N ρ ρ' x a b y y' -
        hairerI2Psi2CovTwo N ρ' ρ x b a y y' + hairerI2Psi2CovTwo N ρ' ρ' x b b y y' =
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos4Two N ρ ρ' a b y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos2Two N ρ ρ' a b y y' q.1 q.2) +
      (i2Psi2Mean N ρ x a y - i2Psi2Mean N ρ' x b y) *
        (i2Psi2Mean N ρ x a y' - i2Psi2Mean N ρ' x b y') := by
  obtain ⟨a4, a2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ ha ha hW hξ hξ x y y'
  obtain ⟨b4, b2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ' ha hb hW hξ hξ' x y y'
  obtain ⟨c4, c2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ hb ha hW hξ' hξ x y y'
  obtain ⟨d4, d2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ' hb hb hW hξ' hξ' x y y'
  have e4 : (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 *
        hairerI2Psi2Kernel N x y' q.2 * i2Psi2DiffChaos4Two N ρ ρ' a b y y' q.1 q.2) =
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ, ρ] ![a, a, a, a] y y' q.1 q.2) -
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) -
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos4Two N ![ρ', ρ', ρ, ρ] ![b, b, a, a] y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos4Two N ![ρ', ρ', ρ', ρ'] ![b, b, b, b] y y' q.1 q.2 := by
    rw [← integral_comb4_cross a4 b4 c4 d4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos4Two]
    ring
  have e2 : (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 *
        hairerI2Psi2Kernel N x y' q.2 * i2Psi2DiffChaos2Two N ρ ρ' a b y y' q.1 q.2) =
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ, ρ] ![a, a, a, a] y y' q.1 q.2) -
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) -
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos2Two N ![ρ', ρ', ρ, ρ] ![b, b, a, a] y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos2Two N ![ρ', ρ', ρ', ρ'] ![b, b, b, b] y y' q.1 q.2 := by
    rw [← integral_comb4_cross a2 b2 c2 d2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos2Two]
    ring
  rw [e4, e2]
  unfold hairerI2Psi2CovTwo i2Psi2Mean
  ring

end RegularityStructures.Phi43

end
