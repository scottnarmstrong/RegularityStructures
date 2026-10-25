/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneFubini
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs

/-!
# The chaos-`1` identity for `I(Ψ³)Ψ²`

With `ρ_z(w) = δK(z, w) Q(w - z)²` the chaos-`1` kernel, the two cross terms with the counterterm
`-3 c Ψ` and `9 c² Q(z - z')` combine to
`36 ∫ (smear ρ_z - (c/2) J(z - ·)) (smear ρ_z' - (c/2) J(z' - ·)) dy`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The weight `ρ_z(w) = δK(z, w) Q(w - z)²`. -/
def i3Psi2Rho (K Q : SpaceTime → ℝ) (z w : SpaceTime) : ℝ := i3Psi2dK K z w * Q (w - z) ^ 2

/-- The chaos-`1` part of the covariance together with the counterterm cross terms. -/
def i3Psi2Chaos1Total (K Q : SpaceTime → ℝ) (c : ℝ) (z z' : SpaceTime) : ℝ :=
  i3Psi2Double K (i3Psi2Chaos1 Q) z z' -
    3 * c * (∫ w, i3Psi2dK K z w * (6 * Q (w - z) ^ 2 * Q (w - z'))) -
    3 * c * (∫ w, i3Psi2dK K z' w * (6 * Q (w - z') ^ 2 * Q (w - z))) +
    9 * c * c * Q (z - z')

theorem i3Psi2Cov_eq (K Q : SpaceTime → ℝ) (c : ℝ) (z z' : SpaceTime) :
    i3Psi2Cov K Q c z z' = i3Psi2Double K (i3Psi2Chaos5 Q) z z' +
      i3Psi2Double K (i3Psi2Chaos3 Q) z z' + i3Psi2Chaos1Total K Q c z z' := by
  unfold i3Psi2Cov i3Psi2Chaos1Total
  ring

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem integrable_i3Psi2Rho {K Q : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) (z : SpaceTime) :
    Integrable (i3Psi2Rho K Q z) := by
  refine (integrable_i3Psi2dK hKi z).mul_bdd (c := MQ ^ 2)
    ((hQm.comp (measurable_id.sub measurable_const)).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hQb _) 2

theorem i3Psi2Double1_eq {K Q : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) (z z' : SpaceTime) :
    i3Psi2Double K (i3Psi2Chaos1 Q) z z' =
      36 * ∫ w, i3Psi2Rho K Q z w * ∫ w', i3Psi2Rho K Q z' w' * Q (w - w') := by
  have iρ := integrable_i3Psi2Rho hKi hQm hQb z
  have iρ' := integrable_i3Psi2Rho hKi hQm hQb z'
  have hprod := iρ.mul_prod iρ'
  have hF : Integrable (fun q : SpaceTime × SpaceTime =>
      i3Psi2Rho K Q z q.1 * i3Psi2Rho K Q z' q.2 * Q (q.1 - q.2)) (volume.prod volume) :=
    hprod.mul_bdd (c := MQ) (hQm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hQb _)
  have e : ∀ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      i3Psi2Chaos1 Q z z' q.1 q.2 =
      36 * (i3Psi2Rho K Q z q.1 * i3Psi2Rho K Q z' q.2 * Q (q.1 - q.2)) := fun q => by
    unfold i3Psi2Chaos1 i3Psi2Kernel1 i3Psi2Rho
    ring
  unfold i3Psi2Double
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have key : ∫ q : SpaceTime × SpaceTime, i3Psi2Rho K Q z q.1 * i3Psi2Rho K Q z' q.2 *
      Q (q.1 - q.2) ∂(volume.prod volume) = ∫ w, ∫ w', i3Psi2Rho K Q z w *
        i3Psi2Rho K Q z' w' * Q (w - w') := integral_prod _ hF
  refine key.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  beta_reduce
  ring

theorem i3Psi2Cross_eq {K Q : SpaceTime → ℝ} (z z' : SpaceTime) :
    ∫ w, i3Psi2dK K z w * (6 * Q (w - z) ^ 2 * Q (w - z')) =
      6 * ∫ w, i3Psi2Rho K Q z w * Q (w - z') := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  unfold i3Psi2Rho
  ring

/-- **The chaos-`1` identity.** -/
theorem i3Psi2Chaos1Total_eq {K J Q : SpaceTime → ℝ} {M MQ c : ℝ} (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hJi : Integrable J) (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) (hKi : Integrable K)
    (z z' : SpaceTime) :
    i3Psi2Chaos1Total K Q c z z' =
      36 * ∫ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
        (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y)) := by
  have iρ := integrable_i3Psi2Rho hKi hQm hQb z
  have iρ' := integrable_i3Psi2Rho hKi hQm hQb z'
  have iS := integrable_i3Psi2Smear iρ hJi
  have iS' := integrable_i3Psi2Smear iρ' hJi
  have bS' := abs_i3Psi2Smear_le hJm hJb iρ'
  have iJz' : Integrable (fun y => J (z' - y)) := integrable_comp_sub_left_spaceTime hJi z'
  have mS : AEStronglyMeasurable (i3Psi2Smear J (i3Psi2Rho K Q z)) := iS.aestronglyMeasurable
  have mS' : AEStronglyMeasurable (i3Psi2Smear J (i3Psi2Rho K Q z')) := iS'.aestronglyMeasurable
  have mJz : AEStronglyMeasurable (fun y => J (z - y)) :=
    (hJm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have mJz' : AEStronglyMeasurable (fun y => J (z' - y)) :=
    (hJm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have i1 : Integrable (fun y => i3Psi2Smear J (i3Psi2Rho K Q z) y *
      i3Psi2Smear J (i3Psi2Rho K Q z') y) :=
    iS.mul_bdd (c := M * ∫ w, |i3Psi2Rho K Q z' w|) mS'
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact bS' y)
  have i2 : Integrable (fun y => i3Psi2Smear J (i3Psi2Rho K Q z) y * J (z' - y)) :=
    iS.mul_bdd (c := M) mJz' (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJb _)
  have i3 : Integrable (fun y => J (z - y) * i3Psi2Smear J (i3Psi2Rho K Q z') y) :=
    iS'.bdd_mul (c := M) mJz (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJb _)
  have i4 : Integrable (fun y => J (z - y) * J (z' - y)) :=
    iJz'.bdd_mul (c := M) mJz (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJb _)
  have e : ∀ y, (i3Psi2Smear J (i3Psi2Rho K Q z) y - c / 2 * J (z - y)) *
      (i3Psi2Smear J (i3Psi2Rho K Q z') y - c / 2 * J (z' - y)) =
      i3Psi2Smear J (i3Psi2Rho K Q z) y * i3Psi2Smear J (i3Psi2Rho K Q z') y -
        c / 2 * (i3Psi2Smear J (i3Psi2Rho K Q z) y * J (z' - y)) -
        c / 2 * (J (z - y) * i3Psi2Smear J (i3Psi2Rho K Q z') y) +
        c / 2 * (c / 2) * (J (z - y) * J (z' - y)) := fun y => by ring
  have j12 : Integrable (fun y => i3Psi2Smear J (i3Psi2Rho K Q z) y *
      i3Psi2Smear J (i3Psi2Rho K Q z') y -
        c / 2 * (i3Psi2Smear J (i3Psi2Rho K Q z) y * J (z' - y))) := i1.sub (i2.const_mul _)
  have j123 : Integrable (fun y => i3Psi2Smear J (i3Psi2Rho K Q z) y *
      i3Psi2Smear J (i3Psi2Rho K Q z') y -
        c / 2 * (i3Psi2Smear J (i3Psi2Rho K Q z) y * J (z' - y)) -
        c / 2 * (J (z - y) * i3Psi2Smear J (i3Psi2Rho K Q z') y)) := j12.sub (i3.const_mul _)
  simp_rw [e]
  rw [integral_add j123 (i4.const_mul _), integral_sub j12 (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
  have A := integral_smear_mul_smear hJm hJb hJi hQJ iρ iρ'
  have B1 := integral_smear_mul_J hJb hJi hQJ iρ z'
  have B2 := integral_smear_mul_J hJb hJi hQJ iρ' z
  have C := integral_J_mul_J hQJ z z'
  have B2' : ∫ y, J (z - y) * i3Psi2Smear J (i3Psi2Rho K Q z') y =
      ∫ w, i3Psi2Rho K Q z' w * Q (w - z) := by
    rw [← B2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce; ring
  rw [A, B1, B2', C]
  unfold i3Psi2Chaos1Total
  rw [i3Psi2Double1_eq hKi hQm hQb, i3Psi2Cross_eq, i3Psi2Cross_eq]
  ring

end RegularityStructures

end
