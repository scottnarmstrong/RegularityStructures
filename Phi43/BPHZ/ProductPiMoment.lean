/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiSecond
public import Phi43.BPHZ.ProductPiAllMoments
public import Phi43.BPHZ.ModelRegPiTreesCore
public import Phi43.BPHZ.PositivePiMoment

/-!
# `q`-th moments of `Q_t Π_x I(Ψ²)Ψ (x)` for the canonical models

`Q_t Π_x I(Ψ²)Ψ (x) = ∫_{ℝ⁴} Q_t(x, y) v₂(x, y) Ψ(proj y) dy = ∫_{ℝ × T³} q^♯_t(x, u) I₂Ψ_{proj x}(u) du`
(periodisation), so the second moment of `productISqPsiField_semigroupPeriodised_second_moment_le`
(exponent `1 - 5κ`) and the moment equivalence give
`∫⁻ ‖Q_t Π_x I(Ψ²)Ψ (x)‖ₑ^q ≤ ofReal (C t^((deg + κ̄)/4))^q` for `κ̄ ≤ κ/2`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `Q_t Π_x I(Ψ²)Ψ (x)` of the canonical model is the semigroup-tested field `I₂Ψ`. -/
theorem regPi_iPsiSqPsi_eq_tested {Ω : Type*} {N : ℕ} {κ : Kappa} {Cst : RenormalisationConstants}
    [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) {ω : Ω} (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
        (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x =
      ∫ u, semigroupPeriodised t x u * productISqPsiField N ρ ε ξ (spaceTimeProj x) ω u := by
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
  rw [regPi_canonicalModelOfLift_eq_integral hf hg _ ht x, extensionPi_iPsiSqPsi_eq hf x]
  have e : ∀ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
      (hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) *
          hairerPsiField N ξ ω (spaceTimeProj y)) =
      parabolicSemigroup.kernel t x y *
        productISqPsiField N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y) := by
    intro y; rw [hfield]
  simp only [e]
  exact (integral_mul_comp_proj_periodise (measurable_parabolicSemigroup_kernel t x) hGm hint).2

/-- **`q`-th moment of `Q_t Π_x I(Ψ²)Ψ (x)`.** -/
theorem regPi_iPsiSqPsi_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiSqPsi + κbar) /
            parabolicSemigroup.order)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨C₀, hC₀, h2⟩ := productISqPsiField_semigroupPeriodised_second_moment_le.{u} N hρ
    (δ := 5 * κ.1) (by linarith) (by linarith)
  obtain ⟨A, hA, hAm⟩ := productISqPsiField_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hg t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  rw [posPi_exponent_eq]
  have hae : (fun ω => (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiSqPsi (1 : ℝ) : Symbol → ℝ) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u *
        productISqPsiField N ρ ε ξ (spaceTimeProj x) ω u := by
    filter_upwards [hg] with ω hgω
    exact regPi_iPsiSqPsi_eq_tested hξ hgω ht0 x
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 (spaceTimeProj x) x
  refine Phi43.regPi_lintegral_enorm_pow_le_core
    (F := fun ω => productISqPsiField N ρ ε ξ (spaceTimeProj x) ω)
    (measurable_productISqPsiField_uncurry N hξ (spaceTimeProj x)) ht0 ht1 x hae hq hA hC₀
    (e := 1 - 5 * κ.1) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  simp only [homogeneity]
  linarith

end RegularityStructures.Phi43

end
