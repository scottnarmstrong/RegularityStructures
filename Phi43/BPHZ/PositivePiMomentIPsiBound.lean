/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentIPsi
import Mathlib.Tactic

/-!
# `q`-th moments of `Q_t Π_x I(Ψ) (x)` for the canonical models

`Q_t Π_x I(Ψ) (x) = ∫ Q_t(x, y) R(x, y) dy` with `R = hairerIPsiRecentred`; Minkowski for the
semigroup (`lintegral_enorm_semigroup_apply_pow_le_two`) and the all-distance bound
`hairerIPsiRecentred_lintegral_enorm_pow_le_all` give
`∫⁻ ‖Q_t Π_x I(Ψ) (x)‖ₑ^q ≤ ofReal (C t^((deg I(Ψ) + κ̄)/4))^q`, and for the difference of two models
with the factor `(ε ∨ ε')^θ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
theorem continuous_hairerIPsiRecentred_right (N : ℕ) (ω : Ω) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (x : ParabolicSpace) : Continuous fun y => hairerIPsiRecentred N ξ ω x y := by
  have hψ := isSmoothOnSpaceTime_hairerPsiField N hξ
  have hC : Continuous (hairerConvolution N (fun w => hairerPsiField N ξ ω (spaceTimeProj w))) :=
    (contDiff_hairerConvolution N (f := fun w => hairerPsiField N ξ ω (spaceTimeProj w))
      hψ).continuous
  have hc : ∀ (w : ParabolicSpace) (j : Fin 3), parabolicCoords w j.succ = w.2 j := by
    intro w j
    fin_cases j <;> rfl
  unfold hairerIPsiRecentred CanonicalData.relCoord
  simp only [hc]
  fun_prop

theorem measurable_hairerIPsiRecentred_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : ParabolicSpace) :
    Measurable fun z : Ω × ParabolicSpace => hairerIPsiRecentred N ξ z.1 x z.2 := by
  have h := (measurable_uncurry_of_continuous_of_measurable
    (u := fun (y : ParabolicSpace) (ω : Ω) => hairerIPsiRecentred N ξ ω x y)
    (fun ω => continuous_hairerIPsiRecentred_right N ω (hξ.1 ω) x)
    (fun y => measurable_hairerIPsiRecentred N hξ x y)).comp measurable_swap
  exact h

/-- **`q`-th moment of `Q_t Π_x I(Ψ) (x)`.** -/
theorem regPi_iPsi_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsi + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := hairerIPsiRecentred_lintegral_enorm_pow_le_all.{u} N hρ κ hκb0 hκb hq
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hs : 0 ≤ homogeneity κ .iPsi + κbar := by
    simp only [homogeneity]; linarith
  have hsm : homogeneity κ .iPsi + κbar ≤ 4 := by
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le_two.{u} hq hs hsm
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hg t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiRecentred N ξ ω x y := by
    filter_upwards [hg] with ω hgω
    rw [regPi_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω _ ht.1 x, extensionPi_iPsi_eq (hξ.1 ω) x]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  exact hM hC₀ x (F := fun ω y => hairerIPsiRecentred N ξ ω x y)
    (measurable_hairerIPsiRecentred_uncurry N hξ x) (fun y => h hW hε hξ x y) ht.1 ht.2

/-- **Two-model difference of `Q_t Π_x I(Ψ) (x)`.** -/
theorem regPi_iPsi_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsi + κbar) /
              parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h⟩ := hairerIPsiRecentred_sub_lintegral_enorm_pow_le_all.{u} N hρ hρ' κ hκb0
    hθ hθκ hq
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hs : 0 ≤ homogeneity κ .iPsi + κbar := by
    simp only [homogeneity]; linarith
  have hsm : homogeneity κ .iPsi + κbar ≤ 4 := by
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le_two.{u} hq hs hsm
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hg hg' t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsi (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) := by
    filter_upwards [hg, hg'] with ω hgω hgω'
    rw [regPi_sub_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω (hξ'.1 ω) hgω' _ ht.1 x,
      extensionPi_iPsi_eq (hξ.1 ω) x, extensionPi_iPsi_eq (hξ'.1 ω) x]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have key := hM (C₀ := C₀ * (max ε ε') ^ θ) (mul_nonneg hC₀ hMx) x
    (F := fun ω y => hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y)
    ((measurable_hairerIPsiRecentred_uncurry N hξ x).sub
      (measurable_hairerIPsiRecentred_uncurry N hξ' x))
    (fun y => h hW hε hε' hξ hξ' x y) ht.1 ht.2
  rw [← mul_assoc] at key
  exact key

end RegularityStructures.Phi43

end
