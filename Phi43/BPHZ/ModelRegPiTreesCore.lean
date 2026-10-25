/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiMoment
public import Phi43.BPHZ.ModelRegPiRandom
public import Phi43.BPHZ.SemigroupTestAllMoments
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationAE

/-!
# The `q`-th moment of a tested tree field in Kolmogorov (`lintegral`) form

`regPi_lintegral_enorm_pow_le_core` is the part of the argument of
`regPi_psi_lintegral_enorm_pow_le` that does not depend on the tree: a random variable `R` that is
almost surely the tested field `∫ F(ω, u) q^♯_t(x, u) du`, with a second moment bound
`C₂ lam^e` (`lam = t^(1/4)`) and the moment equivalence with integrability, satisfies
`∫⁻ ‖R‖ₑ^q ≤ ofReal (max 1 √A √C₂ t^s)^q` for every `s ≤ e / 8` and `t ∈ (0, 1]`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **Tree-independent core of the `q`-th moment bound.** -/
theorem regPi_lintegral_enorm_pow_le_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Ω → ℝ} {F : Ω → SpaceTime → ℝ}
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (x : ParabolicSpace)
    (hae : R =ᵐ[P] fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * F ω u)
    {q : ℕ} (hq : 1 ≤ q) {A C₂ e s : ℝ} (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hs : s ≤ e / 8)
    (hint : Integrable (fun ω => (∫ w, F ω w * semigroupPeriodised t x w) ^ (2 * q)) P)
    (hmom : ∫ ω, (∫ w, F ω w * semigroupPeriodised t x w) ^ (2 * q) ∂P ≤
      A * (∫ ω, (∫ w, F ω w * semigroupPeriodised t x w) ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, |∫ w, F ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
      C₂ * (t ^ (1 / 4 : ℝ)) ^ e) :
    ∫⁻ ω, ‖R ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * t ^ s) ^ q := by
  set Yp : Ω → ℝ := fun ω => ∫ w, F ω w * semigroupPeriodised t x w with hYp
  have hYeq : ∀ ω, ∫ u : SpaceTime, semigroupPeriodised t x u * F ω u = Yp ω :=
    fun ω => integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have hYpm : AEStronglyMeasurable Yp P := by
    have h := measurable_integral_mul_field hF (measurable_semigroupPeriodised t x)
    have e' : Yp = fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * F ω u :=
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

end RegularityStructures.Phi43

end
