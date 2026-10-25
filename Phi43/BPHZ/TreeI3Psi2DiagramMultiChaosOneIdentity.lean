/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePair

/-!
# The chaos-`1` identity for a pair of kernels

`i3Psi2Chaos1TotalPair_eq`: with the notation of `TreeI3Psi2DiagramMultiChaosOnePair`,
`i3Psi2Chaos1TotalPair K Q_aa Q_ab Q_ba Q_bb c_a c_b z z' = 36 ∫ D^a_z D^b_{z'} dy`
(pair version of `i3Psi2Chaos1Total_eq`), and the bilinear expansion for the second difference.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- `Q(x) = ∫ J₁(x + w) J₂(w) dw` is measurable. -/
theorem measurable_Q_of_hQJ {J₁ J₂ Q : SpaceTime → ℝ} (hJ₁m : Measurable J₁)
    (hJ₂m : Measurable J₂) (hQ : ∀ x, Q x = ∫ w, J₁ (x + w) * J₂ w) : Measurable Q := by
  have hint : Measurable (fun q : SpaceTime × SpaceTime => J₁ (q.1 + q.2) * J₂ q.2) :=
    (hJ₁m.comp (measurable_fst.add measurable_snd)).mul (hJ₂m.comp measurable_snd)
  have : Q = fun x => ∫ w, J₁ (x + w) * J₂ w := funext hQ
  rw [this]
  exact hint.stronglyMeasurable.integral_prod_right'.measurable

/-- `|Q| ≤ M₁ ∫ |J₂|` for `Q(x) = ∫ J₁(x + w) J₂(w) dw`, `|J₁| ≤ M₁`. -/
theorem abs_Q_le_pair {J₁ J₂ Q : SpaceTime → ℝ} {M₁ : ℝ} (hJ₁m : Measurable J₁)
    (hJ₂m : Measurable J₂) (hJ₁b : ∀ x, |J₁ x| ≤ M₁) (hJ₂i : Integrable J₂)
    (hQ : ∀ x, Q x = ∫ w, J₁ (x + w) * J₂ w) (x : SpaceTime) :
    |Q x| ≤ M₁ * ∫ w, |J₂ w| := by
  have hM : 0 ≤ M₁ := (abs_nonneg _).trans (hJ₁b 0)
  have i1 : Integrable (fun w => M₁ * |J₂ w|) := hJ₂i.norm.const_mul M₁
  have i2 : Integrable (fun w => |J₁ (x + w) * J₂ w|) := by
    have hm : Measurable (fun w => J₁ (x + w) * J₂ w) :=
      (hJ₁m.comp (measurable_const.add measurable_id)).mul hJ₂m
    refine Integrable.mono' i1 (continuous_abs.measurable.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hJ₁b _) (abs_nonneg _)
  rw [hQ x]
  calc |∫ w, J₁ (x + w) * J₂ w| ≤ ∫ w, |J₁ (x + w) * J₂ w| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => J₁ (x + w) * J₂ w)
    _ ≤ ∫ w, M₁ * |J₂ w| := by
        refine integral_mono i2 i1 fun w => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hJ₁b _) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul]

theorem i3Psi2Double1_pair_eq {K Qaa Qbb Qab : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQaam : Measurable Qaa) (hQbbm : Measurable Qbb) (hQabm : Measurable Qab)
    (hQaab : ∀ x, |Qaa x| ≤ MQ) (hQbbb : ∀ x, |Qbb x| ≤ MQ) (hQabb : ∀ x, |Qab x| ≤ MQ)
    (z z' : SpaceTime) :
    i3Psi2Double K (i3Psi2Chaos1Gen Qaa Qbb Qab) z z' =
      36 * ∫ w, i3Psi2Rho K Qaa z w * ∫ w', i3Psi2Rho K Qbb z' w' * Qab (w - w') := by
  have iρ := integrable_i3Psi2Rho hKi hQaam hQaab z
  have iρ' := integrable_i3Psi2Rho hKi hQbbm hQbbb z'
  have hprod := iρ.mul_prod iρ'
  have hF : Integrable (fun q : SpaceTime × SpaceTime =>
      i3Psi2Rho K Qaa z q.1 * i3Psi2Rho K Qbb z' q.2 * Qab (q.1 - q.2)) (volume.prod volume) :=
    hprod.mul_bdd (c := MQ) (hQabm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hQabb _)
  have e : ∀ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      i3Psi2Chaos1Gen Qaa Qbb Qab z z' q.1 q.2 =
      36 * (i3Psi2Rho K Qaa z q.1 * i3Psi2Rho K Qbb z' q.2 * Qab (q.1 - q.2)) := fun q => by
    unfold i3Psi2Chaos1Gen i3Psi2Kernel1 i3Psi2Rho
    ring
  unfold i3Psi2Double
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have key : ∫ q : SpaceTime × SpaceTime, i3Psi2Rho K Qaa z q.1 * i3Psi2Rho K Qbb z' q.2 *
      Qab (q.1 - q.2) ∂(volume.prod volume) = ∫ w, ∫ w', i3Psi2Rho K Qaa z w *
        i3Psi2Rho K Qbb z' w' * Qab (w - w') := integral_prod _ hF
  refine key.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  beta_reduce
  ring

theorem i3Psi2Cross_pair_eq {K Q Q' : SpaceTime → ℝ} (z z' : SpaceTime) :
    ∫ w, i3Psi2dK K z w * (6 * Q (w - z) ^ 2 * Q' (w - z')) =
      6 * ∫ w, i3Psi2Rho K Q z w * Q' (w - z') := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  unfold i3Psi2Rho
  ring

/-- Boundedness and integrability of `D^a_z`. -/
theorem integrable_and_bdd_i3Psi2D {K Q J : SpaceTime → ℝ} {M MQ : ℝ} (c : ℝ) (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hJi : Integrable J) (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ)
    (hKi : Integrable K) (z : SpaceTime) :
    Integrable (i3Psi2D K Q J c z) ∧
      ∀ y, |i3Psi2D K Q J c z y| ≤ M * (∫ w, |i3Psi2Rho K Q z w|) + |c| / 2 * M := by
  have iρ := integrable_i3Psi2Rho hKi hQm hQb z
  have iS := integrable_i3Psi2Smear iρ hJi
  have bS := abs_i3Psi2Smear_le hJm hJb iρ
  have iJz : Integrable (fun y => J (z - y)) := integrable_comp_sub_left_spaceTime hJi z
  refine ⟨iS.sub (iJz.const_mul _), fun y => ?_⟩
  unfold i3Psi2D
  have h2 : |c / 2 * J (z - y)| ≤ |c| / 2 * M := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hJb _) (by positivity)
  exact (abs_sub _ _).trans (add_le_add (bS y) h2)

/-- **The chaos-`1` identity for a pair of kernels.** -/
theorem i3Psi2Chaos1TotalPair_eq {K Ja Jb Qaa Qab Qba Qbb : SpaceTime → ℝ} {Ma Mb MQ ca cb : ℝ}
    (hJam : Measurable Ja) (hJbm : Measurable Jb) (hJab : ∀ x, |Ja x| ≤ Ma)
    (hJbb : ∀ x, |Jb x| ≤ Mb) (hJai : Integrable Ja) (hJbi : Integrable Jb)
    (hQab : ∀ x, Qab x = ∫ w, Ja (x + w) * Jb w) (hQba : ∀ x, Qba x = ∫ w, Jb (x + w) * Ja w)
    (hQaam : Measurable Qaa) (hQbbm : Measurable Qbb) (hQabm : Measurable Qab)
    (hQaab : ∀ x, |Qaa x| ≤ MQ) (hQbbb : ∀ x, |Qbb x| ≤ MQ) (hQabb : ∀ x, |Qab x| ≤ MQ)
    (hKi : Integrable K) (z z' : SpaceTime) :
    i3Psi2Chaos1TotalPair K Qaa Qab Qba Qbb ca cb z z' =
      36 * ∫ y, i3Psi2D K Qaa Ja ca z y * i3Psi2D K Qbb Jb cb z' y := by
  have iρ := integrable_i3Psi2Rho hKi hQaam hQaab z
  have iρ' := integrable_i3Psi2Rho hKi hQbbm hQbbb z'
  have iS := integrable_i3Psi2Smear iρ hJai
  have iS' := integrable_i3Psi2Smear iρ' hJbi
  have bS' := abs_i3Psi2Smear_le hJbm hJbb iρ'
  have iJz : Integrable (fun y => Ja (z - y)) := integrable_comp_sub_left_spaceTime hJai z
  have iJz' : Integrable (fun y => Jb (z' - y)) := integrable_comp_sub_left_spaceTime hJbi z'
  have mS' : AEStronglyMeasurable (i3Psi2Smear Jb (i3Psi2Rho K Qbb z')) := iS'.aestronglyMeasurable
  have mJz : AEStronglyMeasurable (fun y => Ja (z - y)) :=
    (hJam.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have mJz' : AEStronglyMeasurable (fun y => Jb (z' - y)) :=
    (hJbm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have i1 : Integrable (fun y => i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y *
      i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y) :=
    iS.mul_bdd (c := Mb * ∫ w, |i3Psi2Rho K Qbb z' w|) mS'
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact bS' y)
  have i2 : Integrable (fun y => i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y * Jb (z' - y)) :=
    iS.mul_bdd (c := Mb) mJz' (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJbb _)
  have i3 : Integrable (fun y => Ja (z - y) * i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y) :=
    iS'.bdd_mul (c := Ma) mJz (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJab _)
  have i4 : Integrable (fun y => Ja (z - y) * Jb (z' - y)) :=
    iJz'.bdd_mul (c := Ma) mJz (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hJab _)
  have e : ∀ y, i3Psi2D K Qaa Ja ca z y * i3Psi2D K Qbb Jb cb z' y =
      i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y * i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y -
        cb / 2 * (i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y * Jb (z' - y)) -
        ca / 2 * (Ja (z - y) * i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y) +
        ca / 2 * (cb / 2) * (Ja (z - y) * Jb (z' - y)) := fun y => by
    unfold i3Psi2D
    ring
  have j12 : Integrable (fun y => i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y *
      i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y -
        cb / 2 * (i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y * Jb (z' - y))) := i1.sub (i2.const_mul _)
  have j123 : Integrable (fun y => i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y *
      i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y -
        cb / 2 * (i3Psi2Smear Ja (i3Psi2Rho K Qaa z) y * Jb (z' - y)) -
        ca / 2 * (Ja (z - y) * i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y)) := j12.sub (i3.const_mul _)
  simp_rw [e]
  rw [integral_add j123 (i4.const_mul _), integral_sub j12 (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
  have A := integral_smear_mul_smear_pair hJbm hJab hJbb hJai hJbi hQab hQba iρ iρ'
  have B1 := integral_smear_mul_J_pair hJbb hJai hJbi hQab iρ z'
  have B2 := integral_smear_mul_J_pair hJab hJbi hJai hQba iρ' z
  have C := integral_J_mul_J_pair hQab z z'
  have B2' : ∫ y, Ja (z - y) * i3Psi2Smear Jb (i3Psi2Rho K Qbb z') y =
      ∫ w, i3Psi2Rho K Qbb z' w * Qba (w - z) := by
    rw [← B2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce; ring
  rw [A, B1, B2', C]
  unfold i3Psi2Chaos1TotalPair
  rw [i3Psi2Double1_pair_eq hKi hQaam hQbbm hQabm hQaab hQbbb hQabb, i3Psi2Cross_pair_eq,
    i3Psi2Cross_pair_eq]
  ring

/-- Bilinearity: `∫ (f₁ - f₂)(g₁ - g₂) = ∫ f₁ g₁ - ∫ f₁ g₂ - ∫ f₂ g₁ + ∫ f₂ g₂`. -/
theorem integral_sub_mul_sub_eq {f₁ f₂ g₁ g₂ : SpaceTime → ℝ}
    (h₁₁ : Integrable (fun y => f₁ y * g₁ y)) (h₁₂ : Integrable (fun y => f₁ y * g₂ y))
    (h₂₁ : Integrable (fun y => f₂ y * g₁ y)) (h₂₂ : Integrable (fun y => f₂ y * g₂ y)) :
    ∫ y, (f₁ y - f₂ y) * (g₁ y - g₂ y) =
      (∫ y, f₁ y * g₁ y) - (∫ y, f₁ y * g₂ y) - (∫ y, f₂ y * g₁ y) + ∫ y, f₂ y * g₂ y := by
  have e : ∀ y, (f₁ y - f₂ y) * (g₁ y - g₂ y) =
      f₁ y * g₁ y - f₁ y * g₂ y - f₂ y * g₁ y + f₂ y * g₂ y := fun y => by ring
  simp_rw [e]
  have j1 : Integrable (fun y => f₁ y * g₁ y - f₁ y * g₂ y) := h₁₁.sub h₁₂
  have j2 : Integrable (fun y => f₁ y * g₁ y - f₁ y * g₂ y - f₂ y * g₁ y) := j1.sub h₂₁
  rw [integral_add j2 h₂₂, integral_sub j1 h₂₁, integral_sub h₁₁ h₁₂]

end RegularityStructures

end
