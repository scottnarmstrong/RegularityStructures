/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCore
public import Phi43.BPHZ.ProductIPsiPsiMoments
public import Phi43.BPHZ.ProductIPsiPsiSecondBound
public import Phi43.BPHZ.ProductIPsiPsiSqSecondBound
import Mathlib.Tactic

/-!
# `q`-th moments of `Q_t Π_x I(Ψ)Ψ (x)` and `Q_t Π_x I(Ψ)Ψ² (x)` for the canonical models

[Hai14, (10.2) for `τ = I(Ψ)Ψ` (homogeneity `1 - 2κ`) and `τ = I(Ψ)Ψ²` (homogeneity
`1/2 - 3κ`).]  For the canonical model `canonicalModelOfLift N κ C (ξ ω)` of a regularised noise,
`∫⁻ ‖Q_t Π_x τ (x)‖ₑ^q ≤ ofReal (C t^((deg τ + κ̄)/4))^q` for `κ̄ ≤ κ/2`, uniformly in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x`.  The proof combines `Q_t Π_x τ (x) = ∫ Q_t(x, y) F_x(y) dy`
(`regPi_iPsiPsi_eq_integral_field`), the second moments of the covariance layer
(`hairerIPsiPsiField_semigroup_second_moment_le`, `…Sq…`), the moment equivalence of the chaos
layer (`hairerIPsiPsiField_semigroup_integrable_pow_le`, `…Sq…`) and the core
`regPi_lintegral_enorm_pow_le_core_real`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **`q`-th moment of `Q_t Π_x I(Ψ)Ψ (x)`.** -/
theorem regPi_iPsiPsi_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (_hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiPsi + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := hairerIPsiPsiField_semigroup_second_moment_le.{u} N hρ κ.2.1 κ.2.2
  obtain ⟨A, hA, hAm⟩ := hairerIPsiPsiField_semigroup_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hg t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae : (fun ω => (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y := by
    filter_upwards [hg] with ω hgω
    exact regPi_iPsiPsi_eq_integral_field (hξ.1 ω) hgω ht0 x
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 x
  have h2' : ∫ ω, |∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y| ^ 2 ∂P ≤
      C₂ * (t ^ (1 / 4 : ℝ)) ^ (2 * (1 - 2 * κ.1) + κ.1) := by
    simpa only [sq_abs] using h2 hW hε hξ ht0 ht1 x
  refine regPi_lintegral_enorm_pow_le_core_real
    (F := fun ω => hairerIPsiPsiField N ξ x ω) (measurable_hairerIPsiPsiField_uncurry N hξ x)
    ht0 ht1 x hae hq hA hC₂ ?_ hint hmom h2'
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκb, κ.2.1]

/-- **`q`-th moment of `Q_t Π_x I(Ψ)Ψ² (x)`.** -/
theorem regPi_iPsiPsiSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (_hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ Cst = hairerWickConstant N ρ ε →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiPsiSq (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiPsiSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := hairerIPsiPsiSqField_semigroup_second_moment_le.{u} N hρ κ.2.1 κ.2.2
  obtain ⟨A, hA, hAm⟩ := hairerIPsiPsiSqField_semigroup_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hC1 hg t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae : (fun ω => (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiPsiSq (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ y, parabolicSemigroup.kernel t x y *
        hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y := by
    filter_upwards [hg] with ω hgω
    rw [← hC1]
    exact regPi_iPsiPsiSq_eq_integral_field (hξ.1 ω) hgω ht0 x
  obtain ⟨hint, hmom⟩ := hAm N (hairerWickConstant N ρ ε) hρ hW hε.1 hξ ht0 x
  have h2' : ∫ ω, |∫ y, parabolicSemigroup.kernel t x y *
      hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y| ^ 2 ∂P ≤
      C₂ * (t ^ (1 / 4 : ℝ)) ^ (2 * (1 / 2 - 3 * κ.1) + κ.1) := by
    simpa only [sq_abs] using h2 hW hε hξ ht0 ht1 x
  refine regPi_lintegral_enorm_pow_le_core_real
    (F := fun ω => hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω)
    (measurable_hairerIPsiPsiSqField_uncurry N _ hξ x) ht0 ht1 x hae hq hA hC₂ ?_ hint hmom h2'
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκb, κ.2.1]

end RegularityStructures.Phi43

end
