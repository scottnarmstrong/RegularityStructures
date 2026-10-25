/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneIdentity

/-!
# Splitting the smeared weight into a renormalised and a regular part

With `L = K Q²` and `c = 2 ∫ L`,
`smear J ρ_z (y) - (c/2) J(z - y) = Ā(z - y) - B_z(y)`,
`Ā(x) = ∫ L(v) (J(x - v) - J(x)) dv`, `B_z(y) = ∫ K(-w) Q(w - z)² J(w - y) dw`.
This is [Hai14, p. 171]: `Ā` is `(𝓡L) ⋆ J`, of order `-3 - δ`, and `B_z` is the remainder.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The renormalised convolution `Ā(x) = ∫ L(v) (J(x - v) - J(x)) dv` with `L = K Q²`. -/
def i3Psi2Abar (K J Q : SpaceTime → ℝ) (x : SpaceTime) : ℝ :=
  ∫ v, K v * Q v ^ 2 * (J (x - v) - J x)

/-- The remainder `B_z(y) = ∫ K(-w) Q(w - z)² J(w - y) dw`. -/
def i3Psi2Bz (K J Q : SpaceTime → ℝ) (z y : SpaceTime) : ℝ :=
  ∫ w, K (-w) * Q (w - z) ^ 2 * J (w - y)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem integrable_i3Psi2L {K Q : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) :
    Integrable (fun v => K v * Q v ^ 2) := by
  refine hKi.mul_bdd (c := MQ ^ 2) (hQm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hQb _) 2

theorem i3Psi2_smear_sub_eq {K J Q : SpaceTime → ℝ} {M MQ c : ℝ} (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) (hKi : Integrable K)
    (hc : c = 2 * ∫ x, K x * Q x ^ 2) (z y : SpaceTime) :
    i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y) =
      i3Psi2Abar K J Q (z - y) - i3Psi2Bz K J Q z y := by
  have iL := integrable_i3Psi2L hKi hQm hQb
  have mJ : ∀ a : SpaceTime, AEStronglyMeasurable (fun w => J (a - w)) :=
    fun a => (hJm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have bnd : ∀ a : SpaceTime, ∀ᵐ w ∂(volume : Measure SpaceTime), ‖J (a - w)‖ ≤ M :=
    fun a => Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hJb _
  -- the two pieces of `smear`
  have iA : Integrable (fun w => K (z - w) * Q (w - z) ^ 2 * J (w - y)) := by
    have h1 : Integrable (fun w => K (z - w) * Q (z - w) ^ 2) :=
      integrable_comp_sub_left_spaceTime iL z
    have h2 : Integrable (fun w => K (z - w) * Q (z - w) ^ 2 * J (w - y)) :=
      h1.mul_bdd (c := M) ((hJm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hJb _)
    refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [Q_sub_comm (i3Psi2_Q_neg hQJ) z w]
  have iB : Integrable (fun w => K (-w) * Q (w - z) ^ 2 * J (w - y)) := by
    have h1 : Integrable (fun w => K (-w)) := hKi.comp_neg
    have h2 : Integrable (fun w => K (-w) * Q (w - z) ^ 2) :=
      h1.mul_bdd (c := MQ ^ 2)
        ((hQm.comp (measurable_id.sub measurable_const)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hQb _) 2)
    exact h2.mul_bdd (c := M)
      ((hJm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hJb _)
  have e1 : i3Psi2Smear J (i3Psi2Rho K Q z) y =
      (∫ w, K (z - w) * Q (w - z) ^ 2 * J (w - y)) - i3Psi2Bz K J Q z y := by
    unfold i3Psi2Smear i3Psi2Bz
    rw [← integral_sub iA iB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    unfold i3Psi2Rho i3Psi2dK
    ring
  have e2 : (∫ w, K (z - w) * Q (w - z) ^ 2 * J (w - y)) =
      ∫ v, K v * Q v ^ 2 * J (z - y - v) := by
    have h := integral_comp_sub_left_spaceTime
      (fun w => K (z - w) * Q (z - w) ^ 2 * J (w - y)) z
    have h' : (∫ w, K (z - w) * Q (w - z) ^ 2 * J (w - y)) =
        ∫ w, K (z - w) * Q (z - w) ^ 2 * J (w - y) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      beta_reduce
      rw [Q_sub_comm (i3Psi2_Q_neg hQJ) w z]
    rw [h', ← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have a1 : z - (z - v) = v := by abel
    have a2 : z - v - y = z - y - v := by abel
    simp only [a1, a2]
  have iLJ : Integrable (fun v => K v * Q v ^ 2 * J (z - y - v)) :=
    iL.mul_bdd (c := M) (mJ (z - y)) (bnd (z - y))
  have iLJ0 : Integrable (fun v => K v * Q v ^ 2 * J (z - y)) := iL.mul_const _
  have e3 : c / 2 * J (z - y) = ∫ v, K v * Q v ^ 2 * J (z - y) := by
    rw [integral_mul_const, hc]; ring
  unfold i3Psi2Abar
  have e4 : (∫ v, K v * Q v ^ 2 * (J (z - y - v) - J (z - y))) =
      (∫ v, K v * Q v ^ 2 * J (z - y - v)) - ∫ v, K v * Q v ^ 2 * J (z - y) := by
    rw [← integral_sub iLJ iLJ0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce; ring
  rw [e1, e2, e3, e4]
  ring

end RegularityStructures

end
