/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePotBound
public import Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN1

/-!
# The regular part of the chaos-`1` kernel, difference

`B^a_z(y) = ∫ K(-w) Q_aa(w - z)² J_a(w - y) dw`.  We have
`B^a_z - B^b_z = ∫ K(-w) (Q_aa² - Q_bb²)(w - z) J_a(w - y) dw + ∫ K(-w) Q_bb(w - z)² ΔJ(w - y) dw`,
so `|B^a_z - B^b_z| ≤ Pot_{J_a}(h^Δ_z) + Pot_{ΔJ}(h^b_z)` with `h^Δ_z = |K(-·)| |Q_aa² - Q_bb²|(· - z)`
and `h^b_z = |K(-·)| Q_bb(· - z)²`.  The weight `h^Δ_z` is majorised by
`μ s(w)^(-3) s(z - w)^(-(2+θ+ν))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weight `h^Δ_z(w) = |K(-w)| |Q_a(w - z)² - Q_b(w - z)²|`. -/
def i3Psi2HzDelta (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) : ℝ :=
  |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2|

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2HzDelta_nonneg (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) :
    0 ≤ i3Psi2HzDelta K Qa Qb z w :=
  mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem measurable_i3Psi2HzDelta {K Qa Qb : SpaceTime → ℝ} (hKm : Measurable K)
    (hQa : Measurable Qa) (hQb : Measurable Qb) (z : SpaceTime) :
    Measurable (i3Psi2HzDelta K Qa Qb z) := by
  unfold i3Psi2HzDelta
  have h1 := hKm.comp measurable_neg
  have h2 := hQa.comp (measurable_id.sub (measurable_const (a := z)))
  have h3 := hQb.comp (measurable_id.sub (measurable_const (a := z)))
  exact (continuous_abs.measurable.comp h1).mul
    (continuous_abs.measurable.comp ((h2.pow_const 2).sub (h3.pow_const 2)))

theorem integrable_i3Psi2HzDelta {K Qa Qb : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQa : Measurable Qa) (hQb : Measurable Qb) (hQab : ∀ x, |Qa x| ≤ MQ)
    (hQbb : ∀ x, |Qb x| ≤ MQ) (z : SpaceTime) : Integrable (i3Psi2HzDelta K Qa Qb z) := by
  refine (hKi.comp_neg.abs).mul_bdd (c := 2 * MQ ^ 2)
    (continuous_abs.measurable.comp (((hQa.comp (measurable_id.sub measurable_const)).pow_const 2).sub
      ((hQb.comp (measurable_id.sub measurable_const)).pow_const 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  have a1 : |Qa (w - z) ^ 2| ≤ MQ ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hQab _) 2
  have a2 : |Qb (w - z) ^ 2| ≤ MQ ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hQbb _) 2
  have := abs_sub (Qa (w - z) ^ 2) (Qb (w - z) ^ 2)
  linarith

/-- Majorant of `h^Δ_z`. -/
theorem i3Psi2HzDelta_le {K Qa Qb : SpaceTime → ℝ} {B μ θ ν : ℝ} (hB : 0 ≤ B) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQa : ∀ x, 0 < torusParabolicSize x → |Qa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQb : ∀ x, 0 < torusParabolicSize x → |Qb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Qa x - Qb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ)))
    (hQae : ∀ x, Qa (-x) = Qa x) (hQbe : ∀ x, Qb (-x) = Qb x) {z : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w))
    (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2HzDelta K Qa Qb z w ≤
      (2 * B ^ 3 * μ * 3 ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) := by
  have n3 : (0 : ℝ) ≤ 3 ^ ν := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (2 * B ^ 3 * μ * 3 ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) :=
    mul_nonneg (by positivity) (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 1
  · have hz1t := abs_fst_le_one_of_size_le_one hz1
    have a1 := hK (-w) (by simpa using h0)
    have e1 : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by simp [singularPow]
    have h3 := torusParabolicSize_le_three_of_abs_le_four
      (abs_sub_fst_le_four hz1t (hw.trans (by norm_num)))
    have q1 : |Qa (w - z) - Qb (w - z)| ≤ B * μ * singularPow (1 + θ) z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      exact hΔ _ hzw
    have q2 : |Qa (w - z) + Qb (w - z)| ≤ 2 * B * singularPow 1 z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      have h1 := abs_add_le (Qa (z - w)) (Qb (z - w))
      have h2 := hQa (z - w) hzw
      have h3 := hQb (z - w) hzw
      unfold singularPow
      linarith
    have mul12 : singularPow (1 + θ) z w * singularPow 1 z w = singularPow (1 + θ + 1) z w :=
      singularPow_mul_self (1 + θ) 1 z w hzw
    have loss := singularPow_loss_le (p := 1 + θ + 1) hν hzw h3
    have q3 : |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w) := by
      rw [show Qa (w - z) ^ 2 - Qb (w - z) ^ 2 = (Qa (w - z) - Qb (w - z)) *
        (Qa (w - z) + Qb (w - z)) by ring, abs_mul]
      calc |Qa (w - z) - Qb (w - z)| * |Qa (w - z) + Qb (w - z)|
          ≤ (B * μ * singularPow (1 + θ) z w) * (2 * B * singularPow 1 z w) :=
            mul_le_mul q1 q2 (abs_nonneg _) (mul_nonneg (mul_nonneg hB hμ)
              (singularPow_nonneg _ _ _))
        _ = 2 * B ^ 2 * μ * (singularPow (1 + θ) z w * singularPow 1 z w) := by ring
        _ = 2 * B ^ 2 * μ * singularPow (1 + θ + 1) z w := by rw [mul12]
        _ ≤ 2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have e : 1 + θ + 1 + ν = 2 + θ + ν := by ring
            rw [e] at loss
            exact loss
    unfold i3Psi2HzDelta
    rw [e1] at *
    calc |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        (B * torusParabolicSize (-w) ^ (-(3 : ℝ))) *
          (2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w)) :=
          mul_le_mul a1 q3 (abs_nonneg _) (mul_nonneg hB (Real.rpow_nonneg
            (torusParabolicSize_nonneg _) _))
      _ = _ := by ring
  · have : K (-w) = 0 := by
      apply hKs
      have : (-w).1 = -w.1 := rfl
      rw [this, abs_neg]; exact not_le.1 hw
    unfold i3Psi2HzDelta
    rw [this]
    simpa using hrhs

/-- The weights `K(-w) Q(w - z)² J(w - y)` are integrable in `w`. -/
theorem integrable_Bz_integrand {K J Q : SpaceTime → ℝ} {M MQ : ℝ} (hKi : Integrable K)
    (hJm : Measurable J) (hJb : ∀ x, |J x| ≤ M) (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ)
    (z y : SpaceTime) : Integrable (fun w => K (-w) * Q (w - z) ^ 2 * J (w - y)) := by
  have h1 : Integrable (fun w => K (-w)) := hKi.comp_neg
  have h2 : Integrable (fun w => K (-w) * Q (w - z) ^ 2) :=
    h1.mul_bdd (c := MQ ^ 2)
      ((hQm.comp (measurable_id.sub measurable_const)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hQb _) 2)
  exact h2.mul_bdd (c := M)
    ((hJm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hJb _)

/-- **The difference of the regular parts is dominated by two potentials.** -/
theorem abs_i3Psi2Bz_sub_le_pot {K Ja Jb Qa Qb : SpaceTime → ℝ} {M MQ : ℝ} (hKi : Integrable K)
    (hJam : Measurable Ja) (hJbm : Measurable Jb) (hJab : ∀ x, |Ja x| ≤ M)
    (hJbb : ∀ x, |Jb x| ≤ M) (hQam : Measurable Qa) (hQbm : Measurable Qb)
    (hQab : ∀ x, |Qa x| ≤ MQ) (hQbb : ∀ x, |Qb x| ≤ MQ) (z y : SpaceTime) :
    |i3Psi2Bz K Ja Qa z y - i3Psi2Bz K Jb Qb z y| ≤
      i3Psi2Pot Ja (i3Psi2HzDelta K Qa Qb z) y +
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qb z) y := by
  have iHD := integrable_i3Psi2HzDelta hKi hQam hQbm hQab hQbb z
  have iHb := integrable_i3Psi2Hz hKi hQbm hQbb z
  have mJa : Measurable (fun w => |Ja (w - y)|) :=
    continuous_abs.measurable.comp (hJam.comp (measurable_id.sub measurable_const))
  have mΔ : Measurable (fun w => |Ja (w - y) - Jb (w - y)|) :=
    continuous_abs.measurable.comp ((hJam.comp (measurable_id.sub measurable_const)).sub
      (hJbm.comp (measurable_id.sub measurable_const)))
  have iP1 : Integrable (fun w => i3Psi2HzDelta K Qa Qb z w * |Ja (w - y)|) :=
    iHD.mul_bdd (c := M) mJa.aestronglyMeasurable (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_abs]; exact hJab _)
  have iP2 : Integrable (fun w => i3Psi2Hz K Qb z w * |Ja (w - y) - Jb (w - y)|) :=
    iHb.mul_bdd (c := 2 * M) mΔ.aestronglyMeasurable (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_abs]
      have := abs_sub (Ja (w - y)) (Jb (w - y))
      have := hJab (w - y)
      have := hJbb (w - y)
      linarith)
  have ifa := integrable_Bz_integrand hKi hJam hJab hQam hQab z y
  have ifb := integrable_Bz_integrand hKi hJbm hJbb hQbm hQbb z y
  unfold i3Psi2Bz i3Psi2Pot
  rw [← integral_sub ifa ifb, ← integral_add iP1 iP2]
  have h := norm_integral_le_of_norm_le (iP1.add iP2)
    (f := fun w => K (-w) * Qa (w - z) ^ 2 * Ja (w - y) - K (-w) * Qb (w - z) ^ 2 * Jb (w - y))
    (Filter.Eventually.of_forall fun w => ?_)
  · rw [Real.norm_eq_abs] at h
    exact h
  · rw [Real.norm_eq_abs]
    have e : K (-w) * Qa (w - z) ^ 2 * Ja (w - y) - K (-w) * Qb (w - z) ^ 2 * Jb (w - y) =
        K (-w) * (Qa (w - z) ^ 2 - Qb (w - z) ^ 2) * Ja (w - y) +
          K (-w) * Qb (w - z) ^ 2 * (Ja (w - y) - Jb (w - y)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    simp only [Pi.add_apply, i3Psi2HzDelta, i3Psi2Hz, abs_mul, abs_pow, sq_abs]

end RegularityStructures

end
