/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentPsiXMoment
public import Phi43.BPHZ.PositivePiMomentPsiXReduce
public import Phi43.BPHZ.PositivePiMomentPsiXSub
import Mathlib.Tactic
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationAE

/-!
# `q`-th moments of `Q_t Π_x ΨXᵢ (x)` for the canonical models

`Q_t Π_x ΨXᵢ (x) = ∫_{ℝ⁴} Q_t(x, y) Ψ(proj y) (y - x)ᵢ dy = lam ∫_{ℝ × T³} g_i(u) Ψ(u) du`,
`lam = t^(1/4)`, where `g_i = semigroupPeriodisedCoord t x i` is a semigroup test profile.  The second
moment is `≲ lam` (`hairerPsiField_profile_second_moment_le`), all moments follow by the chaos
moment equivalence, and for `κ̄ ≤ κ`, `t ∈ (0, 1]`:
`∫⁻ ‖Q_t Π_x ΨXᵢ (x)‖ₑ^q ≤ ofReal (C t^((deg ΨXᵢ + κ̄)/4))^q`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **`q`-th moment of `Q_t Π_x ΨXᵢ (x)`.** -/
theorem regPi_psiX_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb : κbar ≤ κ.1) (i : Fin 3) {q : ℕ}
    (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg (Symbol.psiX i) + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨A2, hA2, h2⟩ := hairerPsiField_profile_second_moment_le.{u} N hρ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodisedCoord i
  obtain ⟨A, hA, hAm⟩ := hairerPsiField_profile_integrable_pow_le.{u} q hq
  set Cd : ℝ := max (semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0 (-1))
    0 with hCd
  have hCd0 : 0 ≤ Cd := le_max_right _ _
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd), by positivity, ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hg t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  set lam : ℝ := t ^ (1 / 4 : ℝ) with hlamdef
  have hlam : 0 < lam := Real.rpow_pos_of_pos ht.1 _
  have prof := hB ht.1 ht.2 x
  set g : SpaceTime → ℝ := semigroupPeriodisedCoord t x i with hgdef
  have hgm : Measurable g := prof.measurable
  have hgi : Integrable g := prof.integrable
  set Y : Ω → ℝ := fun ω => ∫ w, hairerPsiField N ξ ω w * g w with hY
  have hYm : Measurable Y := by
    have h := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ) hgm
    have e : Y = fun ω => ∫ w, g w * hairerPsiField N ξ ω w :=
      funext fun ω => integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
    rw [e]
    exact h
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x = lam * Y ω := by
    filter_upwards [hg] with ω hgω
    exact (regPi_psiX_eq_tested (hξ.1 ω) hgω i ht.1 x).1
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ hgm hgi
  have hsec := h2 hW hε hξ prof hlam
  have hD0 : 0 ≤ Real.sqrt (A2 * Cd) * lam ^ (-(1 / 2 : ℝ)) := by positivity
  have hD2 : (Real.sqrt (A2 * Cd) * lam ^ (-(1 / 2 : ℝ))) ^ 2 = A2 * Cd * lam ^ (-1 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  have hY2 : ∫ ω, Y ω ^ 2 ∂P ≤ (Real.sqrt (A2 * Cd) * lam ^ (-(1 / 2 : ℝ))) ^ 2 := by
    rw [hD2]
    have hle : semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0 (-1) ≤ Cd :=
      le_max_left _ _
    calc ∫ ω, Y ω ^ 2 ∂P = ∫ ω, |Y ω| ^ 2 ∂P := by simp only [sq_abs]
      _ ≤ A2 * (semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0 (-1) *
            lam ^ (0 + -1 : ℝ)) := h2 hW hε hξ prof hlam
      _ ≤ A2 * (Cd * lam ^ (0 + -1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle
            (Real.rpow_nonneg hlam.le _)) hA2
      _ = A2 * Cd * lam ^ (-1 : ℝ) := by rw [zero_add]; ring
  have hmoments := Phi43.lintegral_enorm_pow_le_of_moments hYm.aestronglyMeasurable hq hA hD0
    hint hmom hY2
  have e1 : ∀ ω, ‖lam * Y ω‖ₑ ^ q = ENNReal.ofReal lam ^ q * ‖Y ω‖ₑ ^ q := fun ω => by
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal hlam.le]
  simp_rw [e1]
  rw [lintegral_const_mul'' _ (hYm.enorm.pow_const q).aemeasurable]
  refine (mul_le_mul_right hmoments _).trans ?_
  rw [← mul_pow, ← ENNReal.ofReal_mul hlam.le]
  refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
  have hl12 : lam * lam ^ (-(1 / 2 : ℝ)) = lam ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hlam (1 : ℝ) (-(1 / 2 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have hlt : lam ^ (1 / 2 : ℝ) ≤ t ^ ((homogeneity κ (Symbol.psiX i) + κbar) / 4) := by
    rw [hlamdef, ← Real.rpow_mul ht.1.le]
    refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
    have : homogeneity κ (Symbol.psiX i) = 1 / 2 - κ.1 := by simp only [homogeneity]
    rw [this]
    linarith
  calc lam * (max 1 (Real.sqrt A) * (Real.sqrt (A2 * Cd) * lam ^ (-(1 / 2 : ℝ))))
      = max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd) * (lam * lam ^ (-(1 / 2 : ℝ))) := by ring
    _ = max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd) * lam ^ (1 / 2 : ℝ) := by rw [hl12]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlt (by positivity)

/-- **Two-model difference of `Q_t Π_x ΨXᵢ (x)`.** -/
theorem regPi_psiX_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ ≤ κ.1 - κbar) (i : Fin 3) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg (Symbol.psiX i) + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨A2, hA2, h2⟩ := hairerPsiField_profile_sub_second_moment_le.{u} N hρ hρ' hθ hθ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodisedCoord i
  obtain ⟨A, hA, hAm⟩ := hairerPsiField_profile_sub_integrable_pow_le.{u} q hq
  set Cd : ℝ := max (semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0
    (-1 - 2 * θ)) 0 with hCd
  have hCd0 : 0 ≤ Cd := le_max_right _ _
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hg hg' t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  set lam : ℝ := t ^ (1 / 4 : ℝ) with hlamdef
  have hlam : 0 < lam := Real.rpow_pos_of_pos ht.1 _
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have prof := hB ht.1 ht.2 x
  set g : SpaceTime → ℝ := semigroupPeriodisedCoord t x i with hgdef
  have hgm : Measurable g := prof.measurable
  have hgi : Integrable g := prof.integrable
  set Y : Ω → ℝ := fun ω => ∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * g w
    with hY
  have hYm : Measurable Y := by
    have hF : Measurable fun q : Ω × SpaceTime =>
        hairerPsiField N ξ q.1 q.2 - hairerPsiField N ξ' q.1 q.2 :=
      (measurable_hairerPsiField_uncurry N hξ).sub (measurable_hairerPsiField_uncurry N hξ')
    have h := measurable_integral_mul_field
      (F := fun ω u => hairerPsiField N ξ ω u - hairerPsiField N ξ' ω u) hF hgm
    have e : Y = fun ω => ∫ w, g w * (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) :=
      funext fun ω => integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
    rw [e]
    exact h
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x = lam * Y ω := by
    filter_upwards [hg, hg'] with ω hgω hgω'
    obtain ⟨e1, i1⟩ := regPi_psiX_eq_tested (Cst := Cst) (hξ.1 ω) hgω i ht.1 x
    obtain ⟨e2, i2⟩ := regPi_psiX_eq_tested (Cst := Cst') (hξ'.1 ω) hgω' i ht.1 x
    rw [e1, e2, ← mul_sub, hY]
    congr 1
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hgdef]
    ring
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' hgm hgi
  have hsec := h2 hW hε hε' hξ hξ' prof hlam
  set D : ℝ := Real.sqrt (A2 * Cd) * (max ε ε') ^ θ * lam ^ (-(1 / 2 : ℝ) - θ) with hD
  have hD0 : 0 ≤ D := by positivity
  have hD2 : D ^ 2 = A2 * (max ε ε') ^ (2 * θ) * (Cd * lam ^ (0 + (-1 - 2 * θ) : ℝ)) := by
    have hm0 : 0 ≤ max ε ε' := le_max_of_le_left hε.1.le
    have e1 : ((max ε ε') ^ θ) ^ 2 = (max ε ε') ^ (2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
      norm_num [mul_comm]
    have e2 : (lam ^ (-(1 / 2 : ℝ) - θ)) ^ 2 = lam ^ (0 + (-1 - 2 * θ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
      congr 1
      push_cast
      ring
    rw [hD, mul_pow, mul_pow, Real.sq_sqrt (by positivity), e1, e2]
    ring
  have hY2 : ∫ ω, Y ω ^ 2 ∂P ≤ D ^ 2 := by
    rw [hD2]
    have hle : semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0 (-1 - 2 * θ) ≤
        Cd := le_max_left _ _
    calc ∫ ω, Y ω ^ 2 ∂P = ∫ ω, |Y ω| ^ 2 ∂P := by simp only [sq_abs]
      _ ≤ A2 * (max ε ε') ^ (2 * θ) *
            (semigroupTestDoubleConst B (fun r => parabolicMomentConst (r + 1)) 0 (-1 - 2 * θ) *
              lam ^ (0 + (-1 - 2 * θ) : ℝ)) := h2 hW hε hε' hξ hξ' prof hlam
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle
            (Real.rpow_nonneg hlam.le _)) (mul_nonneg hA2 (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _))
  have hmoments := Phi43.lintegral_enorm_pow_le_of_moments hYm.aestronglyMeasurable hq hA hD0
    hint hmom hY2
  have e1 : ∀ ω, ‖lam * Y ω‖ₑ ^ q = ENNReal.ofReal lam ^ q * ‖Y ω‖ₑ ^ q := fun ω => by
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal hlam.le]
  simp_rw [e1]
  rw [lintegral_const_mul'' _ (hYm.enorm.pow_const q).aemeasurable]
  refine (mul_le_mul_right hmoments _).trans ?_
  rw [← mul_pow, ← ENNReal.ofReal_mul hlam.le]
  refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
  have hl12 : lam * lam ^ (-(1 / 2 : ℝ) - θ) = lam ^ (1 / 2 - θ : ℝ) := by
    have h := Real.rpow_add hlam (1 : ℝ) (-(1 / 2 : ℝ) - θ)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hlt : lam ^ (1 / 2 - θ : ℝ) ≤ t ^ ((homogeneity κ (Symbol.psiX i) + κbar) / 4) := by
    rw [hlamdef, ← Real.rpow_mul ht.1.le]
    refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
    have : homogeneity κ (Symbol.psiX i) = 1 / 2 - κ.1 := by simp only [homogeneity]
    rw [this]
    linarith
  calc lam * (max 1 (Real.sqrt A) * D)
      = max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd) * (max ε ε') ^ θ *
          (lam * lam ^ (-(1 / 2 : ℝ) - θ)) := by rw [hD]; ring
    _ = max 1 (Real.sqrt A) * Real.sqrt (A2 * Cd) * (max ε ε') ^ θ * lam ^ (1 / 2 - θ : ℝ) := by
        rw [hl12]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlt (by positivity)

end RegularityStructures.Phi43

end
