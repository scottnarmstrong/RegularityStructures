/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiField
public import Phi43.BPHZ.ModelRegPiTreesCore
public import Phi43.BPHZ.PositivePiMomentIPsiBound
import Mathlib.Tactic

/-!
# Packaging of the `q`-th moment of a tested field on `ℝ⁴`

`regPi_lintegral_enorm_pow_le_core_real` is the `ℝ⁴` analogue of
`regPi_lintegral_enorm_pow_le_core`: a random variable `R` that is almost surely the tested field
`∫ Q_t(x, y) F(ω, y) dy`, with a second moment bound `C₂ lam^e` and the moment equivalence with
integrability, satisfies `∫⁻ ‖R‖ₑ^q ≤ ofReal (max 1 √A √C₂ t^s)^q`.  We also record the joint
measurability of the fields of `I(Ψ)Ψ` and `I(Ψ)(Ψ² - c₁)` in `(ω, y)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The field of `I(Ψ)Ψ` is jointly measurable in `(ω, y)`. -/
theorem measurable_hairerIPsiPsiField_uncurry {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : ParabolicSpace) :
    Measurable fun q : Ω × ParabolicSpace => hairerIPsiPsiField N ξ x q.1 q.2 := by
  have hΨ : Measurable fun q : Ω × ParabolicSpace =>
      hairerPsiField N ξ q.1 (spaceTimeProj q.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
      (f := fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2))
      (measurable_hairerPsiField_uncurry N hξ)
      (measurable_fst.prodMk (continuous_spaceTimeProj.measurable.comp measurable_snd))
  unfold hairerIPsiPsiField
  exact (measurable_hairerIPsiRecentred_uncurry N hξ x).mul hΨ

/-- The field of `I(Ψ)(Ψ² - c₁)` is jointly measurable in `(ω, y)`. -/
theorem measurable_hairerIPsiPsiSqField_uncurry {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (c₁ : ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : ParabolicSpace) :
    Measurable fun q : Ω × ParabolicSpace => hairerIPsiPsiSqField N ξ c₁ x q.1 q.2 := by
  have hΨ : Measurable fun q : Ω × ParabolicSpace =>
      hairerPsiField N ξ q.1 (spaceTimeProj q.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
      (f := fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2))
      (measurable_hairerPsiField_uncurry N hξ)
      (measurable_fst.prodMk (continuous_spaceTimeProj.measurable.comp measurable_snd))
  unfold hairerIPsiPsiSqField hairerTreePsiSq
  exact (measurable_hairerIPsiRecentred_uncurry N hξ x).mul ((hΨ.pow_const 2).sub_const c₁)

/-- The semigroup average of a jointly measurable field is measurable in `ω`. -/
theorem measurable_integral_semigroup_mul_field {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → ParabolicSpace → ℝ} (hF : Measurable fun q : Ω × ParabolicSpace => F q.1 q.2)
    (t : ℝ) (x : ParabolicSpace) :
    Measurable fun ω => ∫ y, parabolicSemigroup.kernel t x y * F ω y :=
  (((((measurable_parabolicSemigroup_kernel t x).comp measurable_snd).mul hF)
    ).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ParabolicSpace))).measurable

/-- **Tree-independent core of the `q`-th moment bound, on `ℝ⁴`.** -/
theorem regPi_lintegral_enorm_pow_le_core_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Ω → ℝ} {F : Ω → ParabolicSpace → ℝ}
    (hF : Measurable fun q : Ω × ParabolicSpace => F q.1 q.2) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : ParabolicSpace)
    (hae : R =ᵐ[P] fun ω => ∫ y, parabolicSemigroup.kernel t x y * F ω y)
    {q : ℕ} (hq : 1 ≤ q) {A C₂ e s : ℝ} (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hs : s ≤ e / 8)
    (hint : Integrable (fun ω => (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ (2 * q)) P)
    (hmom : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ (2 * q) ∂P ≤
      A * (∫ ω, (∫ y, parabolicSemigroup.kernel t x y * F ω y) ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, |∫ y, parabolicSemigroup.kernel t x y * F ω y| ^ 2 ∂P ≤
      C₂ * (t ^ (1 / 4 : ℝ)) ^ e) :
    ∫⁻ ω, ‖R ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * t ^ s) ^ q := by
  set Yp : Ω → ℝ := fun ω => ∫ y, parabolicSemigroup.kernel t x y * F ω y with hYp
  have hYpm : AEStronglyMeasurable Yp P :=
    (measurable_integral_semigroup_mul_field hF t x).aestronglyMeasurable
  simp only [sq_abs] at h2
  set D : ℝ := Real.sqrt C₂ * t ^ (e / 8) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg ht.le _)
  have hD2 : D ^ 2 = C₂ * (t ^ (1 / 4 : ℝ)) ^ e := by
    rw [hD, mul_pow, Real.sq_sqrt hC₂, ← Real.rpow_mul ht.le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    congr 2
    push_cast
    ring
  have h2m : ∫ ω, Yp ω ^ 2 ∂P ≤ D ^ 2 := by rw [hD2]; exact h2
  calc ∫⁻ ω, ‖R ω‖ₑ ^ q ∂P
      = ∫⁻ ω, ‖Yp ω‖ₑ ^ q ∂P :=
        lintegral_congr_ae (hae.mono fun ω h =>
          congrArg (fun r : ℝ => ‖r‖ₑ ^ q) h)
    _ ≤ ENNReal.ofReal (max 1 (Real.sqrt A) * D) ^ q :=
        Phi43.lintegral_enorm_pow_le_of_moments hYpm hq hA hD0 hint hmom h2m
    _ ≤ _ := by
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht ht1 hs)
            (Real.sqrt_nonneg _)) (by positivity)

end RegularityStructures.Phi43

end
