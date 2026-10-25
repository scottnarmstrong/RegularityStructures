/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiMoment
public import Phi43.BPHZ.ProductPiDiffSecond
public import Phi43.BPHZ.ProductPiDiffAllMoments
public import Phi43.BPHZ.ModelRegPiTreesDiffCore

/-!
# Two-model difference of `q`-th moments of `Q_t Π_x I(Ψ²)Ψ (x)`

For two canonical models built from different mollifiers `ρ, ρ'` and scales `ε, ε'` of the same white
noise, with `0 < θ ≤ κ` and `κ̄ ≤ κ/2`,
`∫⁻ ‖Q_t Π_x I(Ψ²)Ψ (x) - Q_t Π'_x I(Ψ²)Ψ (x)‖ₑ^q ≤ ofReal (C (max ε ε')^θ t^((deg + κ̄)/4))^q`
(`regPi_iPsiSqPsi_sub_lintegral_enorm_pow_le`), from the second moment
`productISqPsiField_sub_semigroupPeriodised_second_moment_le` with `δ = 3κ` and the moment
equivalence for differences.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Integrability of the tested field `q^♯_t(x, ·) I₂Ψ_{proj x}` of the canonical model. -/
theorem integrable_tested_iPsiSqPsi {Ω : Type*} {N : ℕ} {κ : Kappa}
    {Cst : RenormalisationConstants} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) {ω : Ω} (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    Integrable (fun u : SpaceTime =>
      semigroupPeriodised t x u * productISqPsiField N ρ ε ξ (spaceTimeProj x) ω u) := by
  have hf := hξ.1 ω
  have hfield : ∀ y : ParabolicSpace,
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) *
          hairerPsiField N ξ ω (spaceTimeProj y) =
      productISqPsiField N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y) := by
    intro y
    rw [hairerKernelIncrementPairing_psiSq_eq_gammaWickSq N hξ]
    rfl
  have hint0 := integrable_kernel_mul_extensionPi (N := N) (κ := κ) (C := Cst) hf hg
    Symbol.iPsiSqPsi ht x
  rw [extensionPi_iPsiSqPsi_eq hf x] at hint0
  have hGm : Measurable (productISqPsiField N ρ ε ξ (spaceTimeProj x) ω) :=
    Measurable.comp (g := fun q : Ω × SpaceTime =>
      productISqPsiField N ρ ε ξ (spaceTimeProj x) q.1 q.2) (f := fun u : SpaceTime => (ω, u))
      (measurable_productISqPsiField_uncurry N hξ _) (measurable_const.prodMk measurable_id)
  have hint : Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      productISqPsiField N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y)) := by
    refine hint0.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfield]
  exact (integral_mul_comp_proj_periodise (measurable_parabolicSemigroup_kernel t x) hGm hint).1

/-- **Two-model difference of `Q_t Π_x I(Ψ²)Ψ (x)`.** -/
theorem regPi_iPsiSqPsi_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ}
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiSqPsi + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨C₀, hC₀, h2⟩ := productISqPsiField_sub_semigroupPeriodised_second_moment_le.{u} N hρ hρ'
    (θ := θ) (δ := 3 * κ.1) hθ (by linarith) (by linarith) (by linarith)
  obtain ⟨A, hA, hAm⟩ := productISqPsiField_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hg hg' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  rw [posPi_exponent_eq]
  have hae₁ : (fun ω => (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u *
        productISqPsiField N ρ ε ξ (spaceTimeProj x) ω u := by
    filter_upwards [hg] with ω hgω
    exact regPi_iPsiSqPsi_eq_tested hξ hgω ht0 x
  have hae₂ : (fun ω => (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u *
        productISqPsiField N ρ' ε' ξ' (spaceTimeProj x) ω u := by
    filter_upwards [hg'] with ω hgω
    exact regPi_iPsiSqPsi_eq_tested hξ' hgω ht0 x
  have hi₁ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime => semigroupPeriodised t x u *
      productISqPsiField N ρ ε ξ (spaceTimeProj x) ω u) := by
    filter_upwards [hg] with ω hgω
    exact integrable_tested_iPsiSqPsi (N := N) (κ := κ) (Cst := Cst) hξ hgω ht0 x
  have hi₂ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime => semigroupPeriodised t x u *
      productISqPsiField N ρ' ε' ξ' (spaceTimeProj x) ω u) := by
    filter_upwards [hg'] with ω hgω
    exact integrable_tested_iPsiSqPsi (N := N) (κ := κ) (Cst := Cst') hξ' hgω ht0 x
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 (spaceTimeProj x) x
  have hM : 0 ≤ max ε ε' := le_max_of_le_left hε.1.le
  refine Phi43.regPi_sub_lintegral_enorm_pow_le_core
    (F₁ := fun ω => productISqPsiField N ρ ε ξ (spaceTimeProj x) ω)
    (F₂ := fun ω => productISqPsiField N ρ' ε' ξ' (spaceTimeProj x) ω)
    (measurable_productISqPsiField_uncurry N hξ (spaceTimeProj x))
    (measurable_productISqPsiField_uncurry N hξ' (spaceTimeProj x)) ht0 ht1 x hae₁ hae₂ hi₁ hi₂
    hq hA hC₀ hM (e := 1 - 3 * κ.1 - 2 * θ) ?_ hint hmom (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  simp only [homogeneity]
  linarith

end RegularityStructures.Phi43

end
