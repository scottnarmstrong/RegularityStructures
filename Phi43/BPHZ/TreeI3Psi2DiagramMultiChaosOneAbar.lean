/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneAbar
public import Phi43.BPHZ.TreeI3Psi2RenormHolder

/-!
# The difference of the renormalised convolutions

`Ā_a(x) = ∫ L_a(v) (J_a(x - v) - J_a(x)) dv`, `L_a = K Q_aa²`.  With `ΔL = K (Q_aa² - Q_bb²)` and
`ΔJ = J_a - J_b`,
`Ā_a - Ā_b = ∫ ΔL (J_a(x - ·) - J_a(x)) + ∫ L_b (ΔJ(x - ·) - ΔJ(x))`.
If `|ΔJ| ≲ μ s^(-(3+θ))` with Hölder increments of exponent `1 - θ` and `|Q_aa - Q_bb| ≲ μ s^(-(1+θ))`
then `|Ā_a - Ā_b|(x) ≤ C μ s(x)^(-(3 + δ/2 + θ))`: the first integral by Lemma 10.16 and the second
by its Hölder variant (`abs_integral_mul_sub_le_holder`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Pointwise bound for `ΔL = K (Q_aa² - Q_bb²)`. -/
theorem abs_i3Psi2DeltaL_le {K Qa Qb : SpaceTime → ℝ} {B μ θ ν : ℝ} (hB : 0 ≤ B) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQa : ∀ x, 0 < torusParabolicSize x → |Qa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQb : ∀ x, 0 < torusParabolicSize x → |Qb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Qa x - Qb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ)))
    {v : SpaceTime} (hv : 0 < torusParabolicSize v) :
    |K v * (Qa v ^ 2 - Qb v ^ 2)| ≤
      (2 * B ^ 3 * μ * 2 ^ ν) * torusParabolicSize v ^ (-(5 + θ + ν)) := by
  have n2 : (0 : ℝ) ≤ 2 ^ ν := Real.rpow_nonneg (by norm_num) _
  have hnn : 0 ≤ (2 * B ^ 3 * μ * 2 ^ ν) * torusParabolicSize v ^ (-(5 + θ + ν)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hv.le _)
  by_cases h1 : |v.1| ≤ 1
  · have h2 : torusParabolicSize v ≤ 2 := by
      have := torusParabolicSize_le_sqrt_add_one h1
      simpa [Real.sqrt_one, one_add_one_eq_two] using this
    have a1 := hK v hv
    have a2 := hΔ v hv
    have a3 : |Qa v + Qb v| ≤ 2 * B * torusParabolicSize v ^ (-(1 : ℝ)) := by
      have := abs_add_le (Qa v) (Qb v)
      have := hQa v hv
      have := hQb v hv
      linarith
    have e : |K v * (Qa v ^ 2 - Qb v ^ 2)| =
        |K v| * (|Qa v - Qb v| * |Qa v + Qb v|) := by
      rw [show Qa v ^ 2 - Qb v ^ 2 = (Qa v - Qb v) * (Qa v + Qb v) by ring, abs_mul, abs_mul]
    rw [e]
    have hs0 := Real.rpow_nonneg hv.le (-(3 : ℝ))
    have hs1 := Real.rpow_nonneg hv.le (-(1 + θ))
    have hs2 := Real.rpow_nonneg hv.le (-(1 : ℝ))
    have hpow : torusParabolicSize v ^ (-(3 : ℝ)) * (torusParabolicSize v ^ (-(1 + θ)) *
        torusParabolicSize v ^ (-(1 : ℝ))) =
        torusParabolicSize v ^ ν * torusParabolicSize v ^ (-(5 + θ + ν)) := by
      rw [← Real.rpow_add hv, ← Real.rpow_add hv, ← Real.rpow_add hv]; congr 1; ring
    have hle : torusParabolicSize v ^ ν ≤ 2 ^ ν := Real.rpow_le_rpow hv.le h2 hν
    have nn := Real.rpow_nonneg hv.le (-(5 + θ + ν))
    calc |K v| * (|Qa v - Qb v| * |Qa v + Qb v|)
        ≤ (B * torusParabolicSize v ^ (-(3 : ℝ))) *
          ((B * μ * torusParabolicSize v ^ (-(1 + θ))) *
            (2 * B * torusParabolicSize v ^ (-(1 : ℝ)))) :=
          mul_le_mul a1 (mul_le_mul a2 a3 (abs_nonneg _) (mul_nonneg (mul_nonneg hB hμ) hs1))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hB hs0)
      _ = (2 * B ^ 3 * μ) * (torusParabolicSize v ^ (-(3 : ℝ)) *
          (torusParabolicSize v ^ (-(1 + θ)) * torusParabolicSize v ^ (-(1 : ℝ)))) := by ring
      _ = (2 * B ^ 3 * μ) * (torusParabolicSize v ^ ν * torusParabolicSize v ^ (-(5 + θ + ν))) := by
          rw [hpow]
      _ ≤ (2 * B ^ 3 * μ) * (2 ^ ν * torusParabolicSize v ^ (-(5 + θ + ν))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle nn) (by positivity)
      _ = _ := by ring
  · rw [hKs v (not_le.1 h1)]
    simpa using hnn

/-- Integrability of `L(v) (J(x - v) - J(x))` for integrable `L` and bounded measurable `J`. -/
theorem integrable_mul_sub_of_bdd {L J : SpaceTime → ℝ} {M : ℝ} (hL : Integrable L)
    (hJm : Measurable J) (hJb : ∀ x, |J x| ≤ M) (x : SpaceTime) :
    Integrable (fun v => L v * (J (x - v) - J x)) := by
  refine hL.mul_bdd (c := 2 * M) ((hJm.comp (measurable_const.sub measurable_id)).sub
    measurable_const).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  have := abs_sub (J (x - v)) (J x)
  have := hJb (x - v)
  have := hJb x
  linarith

/-- **The difference of the renormalised convolutions.** -/
theorem abs_i3Psi2Abar_sub_le {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ M MQ : ℝ}, 0 ≤ μ →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      Integrable K → Measurable K → Measurable Ja → Measurable Jb → Measurable Qaa →
      Measurable Qbb → (∀ x, |Ja x| ≤ M) → (∀ x, |Jb x| ≤ M) → (∀ x, |Qaa x| ≤ MQ) →
      (∀ x, |Qbb x| ≤ MQ) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |Ja (u + h) - Ja u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qaa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qbb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Qaa x - Qbb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Ja x - Jb x| ≤ B * μ * torusParabolicSize x ^ (-(3 + θ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤
            B * μ * torusParabolicSize h ^ (1 - θ) * torusParabolicSize u ^ (-(3 + θ) - (1 - θ))) →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |i3Psi2Abar K Ja Qaa x - i3Psi2Abar K Jb Qbb x| ≤
          C * μ * torusParabolicSize x ^ (-(3 + δ / 2 + θ)) := by
  have hν : 0 < δ / 2 := by linarith
  obtain ⟨C1, hC1, h1⟩ := abs_integral_mul_sub_le (a₁ := 5 + θ + δ / 2) (a₂ := 3) (by linarith)
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨C2, hC2, h2⟩ := abs_integral_mul_sub_le_holder (a₁ := 5 + δ / 2) (a₂ := 3 + θ)
    (lam := 1 - θ) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have n2 : (0 : ℝ) ≤ 2 ^ (δ / 2) := Real.rpow_nonneg (by norm_num) _
  refine ⟨C1 * (2 * B ^ 3 * 2 ^ (δ / 2)) * B + C2 * (B ^ 3 * 2 ^ (δ / 2)) * B,
    by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ M MQ hμ hKs hKi hKm hJam hJbm hQam hQbm hJab hJbb hQab hQbb hK hJa
    hJainc hQa hQb hΔQ hΔJ hΔJinc x hx
  have iLa : Integrable (fun v => K v * Qaa v ^ 2) := integrable_i3Psi2L hKi hQam hQab
  have iLb : Integrable (fun v => K v * Qbb v ^ 2) := integrable_i3Psi2L hKi hQbm hQbb
  have iΔL : Integrable (fun v => K v * (Qaa v ^ 2 - Qbb v ^ 2)) :=
    (iLa.sub iLb).congr (Filter.Eventually.of_forall fun v => by simp only [Pi.sub_apply]; ring)
  have p1 := integrable_mul_sub_of_bdd iΔL hJam hJab x
  have p2 : Integrable (fun v => K v * Qbb v ^ 2 * ((Ja (x - v) - Jb (x - v)) - (Ja x - Jb x))) :=
    integrable_mul_sub_of_bdd (J := fun y => Ja y - Jb y) iLb (hJam.sub hJbm) (M := 2 * M)
      (fun y => by
        have := abs_sub (Ja y) (Jb y)
        have := hJab y
        have := hJbb y
        linarith) x
  have pa := integrable_mul_sub_of_bdd iLa hJam hJab x
  have pb := integrable_mul_sub_of_bdd iLb hJbm hJbb x
  have split : i3Psi2Abar K Ja Qaa x - i3Psi2Abar K Jb Qbb x =
      (∫ v, K v * (Qaa v ^ 2 - Qbb v ^ 2) * (Ja (x - v) - Ja x)) +
      ∫ v, K v * Qbb v ^ 2 * ((Ja (x - v) - Jb (x - v)) - (Ja x - Jb x)) := by
    unfold i3Psi2Abar
    rw [← integral_add p1 p2, ← integral_sub pa pb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only
    ring
  rw [split]
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |Ja (u + h) - Ja u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(3 : ℝ) - 1) := by
    intro u h hu hh
    have e : (-(3 : ℝ) - 1) = -(4 : ℝ) := by norm_num
    rw [e]; exact hJainc u h hu hh
  have t1 := h1 (f₁ := fun v => K v * (Qaa v ^ 2 - Qbb v ^ 2)) (f₂ := Ja)
    (B₁ := 2 * B ^ 3 * μ * 2 ^ (δ / 2)) (B₂ := B) (by positivity) hB
    (fun v hv => abs_i3Psi2DeltaL_le (θ := θ) (ν := δ / 2) hB hμ hν.le hKs hK hQa hQb hΔQ hv)
    hJa hinc' x hx
  have t2 := h2 (f₁ := fun v => K v * Qbb v ^ 2) (f₂ := fun y => Ja y - Jb y)
    (B₁ := B ^ 3 * 2 ^ (δ / 2)) (B₂ := B * μ) (by positivity) (by positivity)
    (fun v hv => abs_i3Psi2L_le hB hν.le hKs hK hQb hv) hΔJ hΔJinc x hx
  have e1 : min 0 (5 - (5 + θ + δ / 2) - 3 : ℝ) = -(3 + δ / 2 + θ) := by
    rw [min_eq_right (by linarith)]; ring
  have e2 : (5 - (5 + δ / 2) - (3 + θ) : ℝ) = -(3 + δ / 2 + θ) := by ring
  rw [e1] at t1
  rw [e2] at t2
  refine (abs_add_le _ _).trans ?_
  have hp := Real.rpow_nonneg hx.le (-(3 + δ / 2 + θ))
  calc _ ≤ C1 * (2 * B ^ 3 * μ * 2 ^ (δ / 2)) * B * torusParabolicSize x ^ (-(3 + δ / 2 + θ)) +
        C2 * (B ^ 3 * 2 ^ (δ / 2)) * (B * μ) * torusParabolicSize x ^ (-(3 + δ / 2 + θ)) :=
        add_le_add t1 t2
    _ = _ := by ring

end RegularityStructures

end
