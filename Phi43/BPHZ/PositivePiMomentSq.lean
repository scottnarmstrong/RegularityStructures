/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentLinear
import Mathlib.Tactic

/-!
# `q`-th moments of `Q_t Π_x I(Ψ²) (x)` and `Q_t Π_x I(Ψ³) (x)` for the canonical models

For the canonical model `canonicalModelOfLift N κ C (ξ ω)` of a regularised noise,
`∫⁻ ‖Q_t Π_x τ (x)‖ₑ^q ≤ ofReal (C t^((deg τ + κ̄)/4))^q` for `τ = I(Ψ²), I(Ψ³)`, and the same for
the difference of two models with the factor `(ε ∨ ε')^θ`.  The proof is Minkowski's inequality for
the semigroup average of `v₂`, `v₃` (`lintegral_enorm_semigroup_apply_pow_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **`q`-th moment of `Q_t Π_x I(Ψ²) (x)`.** -/
theorem regPi_iPsiSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := gammaWickSq_lintegral_enorm_pow_le_all.{u} N hρ hκb0 hκb hq
  have hs : 0 ≤ homogeneity κ .iPsiSq + κbar := by
    have := κ.2.1
    have := κ.2.2
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hg t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
    filter_upwards [hg] with ω hgω
    rw [regPi_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω _ ht.1 x, extensionPi_iPsiSq_eq (hξ.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hairerKernelIncrementPairing_psiSq_eq_gammaWickSq N hξ]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  exact hM hC₀ x (measurable_gammaWickSq_proj N hξ (spaceTimeProj x))
    (fun y => h hW hε hξ x y) ht.1

/-- **`q`-th moment of `Q_t Π_x I(Ψ³) (x)`.** -/
theorem regPi_iPsiCube_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ Cst = hairerWickConstant N ρ ε →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCube + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := gammaWickCube_lintegral_enorm_pow_le_all.{u} N hρ hκb0 hκb hq
  have hs : 0 ≤ homogeneity κ .iPsiCube + κbar := by
    have := κ.2.1
    have := κ.2.2
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hC1 hg t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
    filter_upwards [hg] with ω hgω
    rw [regPi_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω _ ht.1 x, extensionPi_iPsiCube_eq (hξ.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hC1, hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  exact hM hC₀ x (measurable_gammaWickCube_proj N hξ (spaceTimeProj x))
    (fun y => h hW hε hξ x y) ht.1

/-- **Two-model difference of `Q_t Π_x I(Ψ²) (x)`.** -/
theorem regPi_iPsiSq_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
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
            (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiSq + κbar) /
              parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := gammaWickSq_sub_lintegral_enorm_pow_le_all.{u} N hρ hρ' hκb0 hκb hθ hθκ hq
  have hs : 0 ≤ homogeneity κ .iPsiSq + κbar := by
    have := κ.2.1
    have := κ.2.2
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hg hg' t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          gammaWickSq N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) := by
    filter_upwards [hg, hg'] with ω hgω hgω'
    rw [regPi_sub_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω (hξ'.1 ω) hgω' _ ht.1 x,
      extensionPi_iPsiSq_eq (hξ.1 ω) x, extensionPi_iPsiSq_eq (hξ'.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hairerKernelIncrementPairing_psiSq_eq_gammaWickSq N hξ, hairerKernelIncrementPairing_psiSq_eq_gammaWickSq N hξ']
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have := hM (mul_nonneg hC₀ hMx) x
    (F := fun ω y => gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
      gammaWickSq N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω)
    ((measurable_gammaWickSq_proj N hξ (spaceTimeProj x)).sub
      (measurable_gammaWickSq_proj N hξ' (spaceTimeProj x)))
    (fun y => h hW hε hε' hξ hξ' x y) ht.1
  simpa [mul_assoc] using this

/-- **Two-model difference of `Q_t Π_x I(Ψ³) (x)`.** -/
theorem regPi_iPsiCube_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      C₁ Cst = hairerWickConstant N ρ ε → C₁ Cst' = hairerWickConstant N ρ' ε' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCube + κbar) /
              parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_all.{u} N hρ hρ' hκb0 hκb hθ hθκ hq
  have hs : 0 ≤ homogeneity κ .iPsiCube + κbar := by
    have := κ.2.1
    have := κ.2.2
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hC1 hC1' hg hg' t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) := by
    filter_upwards [hg, hg'] with ω hgω hgω'
    rw [regPi_sub_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω (hξ'.1 ω) hgω' _ ht.1 x,
      extensionPi_iPsiCube_eq (hξ.1 ω) x, extensionPi_iPsiCube_eq (hξ'.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hC1, hC1', hairerKernelIncrementPairing_psiCube_eq_gammaWickCube, hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have := hM (mul_nonneg hC₀ hMx) x
    (F := fun ω y => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
      gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω)
    ((measurable_gammaWickCube_proj N hξ (spaceTimeProj x)).sub
      (measurable_gammaWickCube_proj N hξ' (spaceTimeProj x)))
    (fun y => h hW hε hε' hξ hξ' x y) ht.1
  simpa [mul_assoc] using this

end RegularityStructures.Phi43

end
