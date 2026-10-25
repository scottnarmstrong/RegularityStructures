/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiBound
public import Phi43.BPHZ.ProductIPsiPsiDiffMoments
public import Phi43.BPHZ.ProductIPsiPsiDiffBound
import Mathlib.Tactic

/-!
# `q`-th moments of the two-mollifier difference of `Q_t Π_x I(Ψ)Ψ (x)`

[Hai14, (10.3) for `τ = I(Ψ)Ψ`.]  For the canonical models of two regularised noises (mollifiers
`ρ, ρ'`, scales `ε, ε' ∈ (0, 1]`) and `κ̄ + θ ≤ κ/2`,
`∫⁻ ‖Q_t Π_x τ (x) - Q_t Π'_x τ (x)‖ₑ^q ≤ ofReal (C (ε ∨ ε')^θ t^((deg τ + κ̄)/4))^q`.
It combines the identities `regPi_iPsiPsi_eq_integral_field`, the difference second moment
`hairerIPsiPsiField_semigroup_sub_second_moment_le`, the difference moment equivalence
`hairerIPsiPsiField_semigroup_sub_integrable_pow_le` and `regPi_lintegral_enorm_pow_le_core_real`
for the field `F_x - F'_x`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **`q`-th moment of the two-mollifier difference of `Q_t Π_x I(Ψ)Ψ (x)`.** -/
theorem regPi_iPsiPsi_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiPsi + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hθκ : θ ≤ κ.1 / 2 := by linarith
  obtain ⟨C₂, hC₂, h2⟩ :=
    hairerIPsiPsiField_semigroup_sub_second_moment_le.{u} N hρ hρ' κ.2.1 κ.2.2 hθ hθκ
  obtain ⟨A, hA, hAm⟩ := hairerIPsiPsiField_semigroup_sub_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hg hg' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  set F : Ω → ParabolicSpace → ℝ := fun ω y =>
    hairerIPsiPsiField N ξ x ω y - hairerIPsiPsiField N ξ' x ω y with hF
  have hFm : Measurable fun q : Ω × ParabolicSpace => F q.1 q.2 :=
    (measurable_hairerIPsiPsiField_uncurry N hξ x).sub (measurable_hairerIPsiPsiField_uncurry N hξ' x)
  have hYeq : ∀ᵐ ω ∂P, (∫ y, parabolicSemigroup.kernel t x y * F ω y) =
      (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
        ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y := by
    filter_upwards [ae_integrable_semigroup_hairerIPsiPsiField N hρ hW hε.1 hξ ht0 x,
      ae_integrable_semigroup_hairerIPsiPsiField N hρ' hW hε'.1 hξ' ht0 x] with ω h₁ h₂
    rw [← integral_sub h₁ h₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, mul_sub]
  have hae : (fun ω => (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ y, parabolicSemigroup.kernel t x y * F ω y := by
    filter_upwards [hg, hg', hYeq] with ω hgω hgω' hY
    rw [hY, regPi_iPsiPsi_eq_integral_field (hξ.1 ω) hgω ht0 x,
      regPi_iPsiPsi_eq_integral_field (hξ'.1 ω) hgω' ht0 x]
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x
  have hpow : ∀ n : ℕ, (fun ω => (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ n) =ᵐ[P]
      fun ω => ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
        ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ n := fun n =>
    hYeq.mono fun ω hω => by simp only [hω]
  have hint' := hint.congr (hpow (2 * q)).symm
  have hmom' : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ (2 * q) ∂P ≤
      A * (∫ ω, (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ 2 ∂P) ^ q := by
    rw [integral_congr_ae (hpow (2 * q)), integral_congr_ae (hpow 2)]
    exact hmom
  have h2' : ∫ ω, |∫ y, parabolicSemigroup.kernel t x y * F ω y| ^ 2 ∂P ≤
      (C₂ * (max ε ε') ^ (2 * θ)) * (t ^ (1 / 4 : ℝ)) ^ (2 * (1 - 2 * κ.1) + κ.1 - 2 * θ) := by
    simp only [sq_abs]
    rw [integral_congr_ae (hpow 2)]
    exact h2 hW hε hε' hξ hξ' ht0 ht1 x
  have hMx : 0 ≤ max ε ε' := le_max_of_le_left hε.1.le
  have hC₂' : 0 ≤ C₂ * (max ε ε') ^ (2 * θ) := mul_nonneg hC₂ (Real.rpow_nonneg hMx _)
  have key := regPi_lintegral_enorm_pow_le_core_real hFm ht0 ht1 x hae hq hA hC₂'
    (s := ((phi43RegularityStructure κ).deg Symbol.iPsiPsi + κbar) / parabolicSemigroup.order)
    (by
      have h : parabolicSemigroup.order = 4 := rfl
      rw [h, phi43RegularityStructure_deg]
      simp only [homogeneity]
      linarith) hint' hmom' h2'
  refine key.trans (le_of_eq ?_)
  congr 2
  have hs : Real.sqrt ((max ε ε') ^ (2 * θ)) = (max ε ε') ^ θ := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.rpow_nonneg hMx _) (Real.rpow_nonneg hMx _),
      ← Real.rpow_add' hMx (by linarith)]
    ring_nf
  rw [Real.sqrt_mul hC₂, hs]
  ring

end RegularityStructures.Phi43

end
