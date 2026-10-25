/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTreesCore
public import Phi43.BPHZ.ModelRegPiTreesDiffCore
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationAE

/-!
# Cores of the `q`-th moment bounds for an arbitrary measurable test function

`regPi_lintegral_enorm_pow_le_core_of_test` and `regPi_sub_lintegral_enorm_pow_le_core_of_test`
are `regPi_lintegral_enorm_pow_le_core` and `regPi_sub_lintegral_enorm_pow_le_core` with the
periodised semigroup kernel `q^♯_t(x, ·)` replaced by an arbitrary measurable test function `g`
(used for the coordinate-weighted kernel of `Ψ² Xᵢ`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **Tree- and test-independent core of the `q`-th moment bound.** -/
theorem regPi_lintegral_enorm_pow_le_core_of_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : SpaceTime → ℝ} (hg : Measurable g) {R : Ω → ℝ} {F : Ω → SpaceTime → ℝ}
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hae : R =ᵐ[P] fun ω => ∫ u : SpaceTime, g u * F ω u)
    {q : ℕ} (hq : 1 ≤ q) {A C₂ e s : ℝ} (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hs : s ≤ e / 8)
    (hint : Integrable (fun ω => (∫ w, F ω w * g w) ^ (2 * q)) P)
    (hmom : ∫ ω, (∫ w, F ω w * g w) ^ (2 * q) ∂P ≤
      A * (∫ ω, (∫ w, F ω w * g w) ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, |∫ w, F ω w * g w| ^ 2 ∂P ≤
      C₂ * (t ^ (1 / 4 : ℝ)) ^ e) :
    ∫⁻ ω, ‖R ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * t ^ s) ^ q := by
  set Yp : Ω → ℝ := fun ω => ∫ w, F ω w * g w with hYp
  have hYeq : ∀ ω, ∫ u : SpaceTime, g u * F ω u = Yp ω :=
    fun ω => integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have hYpm : AEStronglyMeasurable Yp P := by
    have h := measurable_integral_mul_field hF hg
    have e' : Yp = fun ω => ∫ u : SpaceTime, g u * F ω u :=
      funext fun ω => (hYeq ω).symm
    rw [e']
    exact h.aestronglyMeasurable
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
          congrArg (fun r : ℝ => ‖r‖ₑ ^ q) (h.trans (hYeq ω)))
    _ ≤ ENNReal.ofReal (max 1 (Real.sqrt A) * D) ^ q :=
        lintegral_enorm_pow_le_of_moments hYpm hq hA hD0 hint hmom h2m
    _ ≤ _ := by
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht ht1 hs)
            (Real.sqrt_nonneg _)) (by positivity)

/-- **Tree- and test-independent core of the `q`-th moment bound for differences.** -/
theorem regPi_sub_lintegral_enorm_pow_le_core_of_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : SpaceTime → ℝ} (hg : Measurable g) {R R' : Ω → ℝ} {F₁ F₂ : Ω → SpaceTime → ℝ}
    (hF₁ : Measurable fun q : Ω × SpaceTime => F₁ q.1 q.2)
    (hF₂ : Measurable fun q : Ω × SpaceTime => F₂ q.1 q.2) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hae₁ : R =ᵐ[P] fun ω => ∫ u : SpaceTime, g u * F₁ ω u)
    (hae₂ : R' =ᵐ[P] fun ω => ∫ u : SpaceTime, g u * F₂ ω u)
    (hi₁ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime => g u * F₁ ω u))
    (hi₂ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime => g u * F₂ ω u))
    {q : ℕ} (hq : 1 ≤ q) {A C₂ e s M θ : ℝ} (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M)
    (hs : s ≤ e / 8)
    (hint : Integrable (fun ω => (∫ w, (F₁ ω w - F₂ ω w) * g w) ^ (2 * q)) P)
    (hmom : ∫ ω, (∫ w, (F₁ ω w - F₂ ω w) * g w) ^ (2 * q) ∂P ≤
      A * (∫ ω, (∫ w, (F₁ ω w - F₂ ω w) * g w) ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, |∫ w, (F₁ ω w - F₂ ω w) * g w| ^ 2 ∂P ≤
      C₂ * M ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ e) :
    ∫⁻ ω, ‖R ω - R' ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * M ^ θ * t ^ s) ^ q := by
  set Yp : Ω → ℝ := fun ω => ∫ w, (F₁ ω w - F₂ ω w) * g w with hYp
  have hae : (fun ω => R ω - R' ω) =ᵐ[P] Yp := by
    filter_upwards [hae₁, hae₂, hi₁, hi₂] with ω h1 h2 i1 i2
    rw [h1, h2, ← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hYpm : AEStronglyMeasurable Yp P := by
    have h := measurable_integral_mul_field (F := fun ω u => F₁ ω u - F₂ ω u) (hF₁.sub hF₂)
      hg
    have e' : Yp = fun ω => ∫ u : SpaceTime, g u * (F₁ ω u - F₂ ω u) :=
      funext fun ω => integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
    rw [e']
    exact h.aestronglyMeasurable
  simp only [sq_abs] at h2
  set D : ℝ := Real.sqrt C₂ * M ^ θ * t ^ (e / 8) with hD
  have hMθ : 0 ≤ M ^ θ := Real.rpow_nonneg hM _
  have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hMθ) (Real.rpow_nonneg ht.le _)
  have hD2 : D ^ 2 = C₂ * M ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ e := by
    have h1 : (M ^ θ) ^ 2 = M ^ (2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
      congr 1
      push_cast
      ring
    have h3 : (t ^ (e / 8)) ^ 2 = (t ^ (1 / 4 : ℝ)) ^ e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    rw [hD, mul_pow, mul_pow, Real.sq_sqrt hC₂, h1, h3]
  have h2m : ∫ ω, Yp ω ^ 2 ∂P ≤ D ^ 2 := by rw [hD2]; exact h2
  calc ∫⁻ ω, ‖R ω - R' ω‖ₑ ^ q ∂P
      = ∫⁻ ω, ‖Yp ω‖ₑ ^ q ∂P :=
        lintegral_congr_ae (hae.mono fun ω h => congrArg (fun r : ℝ => ‖r‖ₑ ^ q) h)
    _ ≤ ENNReal.ofReal (max 1 (Real.sqrt A) * D) ^ q :=
        lintegral_enorm_pow_le_of_moments hYpm hq hA hD0 hint hmom h2m
    _ ≤ _ := by
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
        have hst : t ^ (e / 8) ≤ t ^ s := Real.rpow_le_rpow_of_exponent_ge ht ht1 hs
        have hc : 0 ≤ Real.sqrt C₂ * M ^ θ := mul_nonneg (Real.sqrt_nonneg _) hMθ
        calc max 1 (Real.sqrt A) * D = max 1 (Real.sqrt A) * ((Real.sqrt C₂ * M ^ θ) * t ^ (e / 8)) := by
              rw [hD]
          _ ≤ max 1 (Real.sqrt A) * ((Real.sqrt C₂ * M ^ θ) * t ^ s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hst hc)
                (le_trans zero_le_one (le_max_left _ _))
          _ = _ := by ring

end RegularityStructures.Phi43

end
