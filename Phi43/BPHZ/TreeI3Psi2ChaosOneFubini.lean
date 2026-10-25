/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneBasic
public import Mathlib.Analysis.Convolution

/-!
# Fubini identities for the chaos-`1` part of `I(Ψ³)Ψ²`

For an integrable `h` write `smear J h (y) = ∫ h(w) J(w - y) dw`.  With `Q(x) = ∫ J(x + w) J(w) dw`
and `J` bounded and integrable:

* `integral_smear_mul_smear`: `∫ smear h₁ · smear h₂ dy = ∫ h₁(w) ∫ h₂(w') Q(w - w') dw' dw`;
* `integral_smear_mul_J`: `∫ smear h (y) J(p - y) dy = ∫ h(w) Q(w - p) dw`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The smearing `y ↦ ∫ h(w) J(w - y) dw`. -/
def i3Psi2Smear (J h : SpaceTime → ℝ) (y : SpaceTime) : ℝ := ∫ w, h w * J (w - y)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem integrable_smear_prod {J h : SpaceTime → ℝ} (hh : Integrable h) (hJi : Integrable J) :
    Integrable (fun p : SpaceTime × SpaceTime => h p.2 * J (p.2 - p.1)) (volume.prod volume) := by
  have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hh hJi.comp_neg
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [neg_sub]

theorem integrable_i3Psi2Smear {J h : SpaceTime → ℝ} (hh : Integrable h) (hJi : Integrable J) :
    Integrable (i3Psi2Smear J h) :=
  (integrable_smear_prod hh hJi).integral_prod_left

theorem abs_i3Psi2Smear_le {J h : SpaceTime → ℝ} {M : ℝ} (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hh : Integrable h) (y : SpaceTime) :
    |i3Psi2Smear J h y| ≤ M * ∫ w, |h w| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hJb 0)
  have i1 : Integrable (fun w => M * |h w|) := hh.norm.const_mul M
  have hm : Measurable (fun w => J (w - y)) := hJm.comp (measurable_id.sub measurable_const)
  have i2' : Integrable (fun w => h w * J (w - y)) := by
    refine Integrable.mono' i1 (hh.aestronglyMeasurable.mul hm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hJb _) (abs_nonneg _)
  have i2 : Integrable (fun w => |h w * J (w - y)|) := i2'.abs
  unfold i3Psi2Smear
  calc |∫ w, h w * J (w - y)| ≤ ∫ w, |h w * J (w - y)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => h w * J (w - y))
    _ ≤ ∫ w, M * |h w| := by
        refine integral_mono i2 i1 fun w => ?_
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hJb _) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul]

/-- The general Fubini swap for a smeared function against a bounded integrable function. -/
theorem integral_smear_mul {J h ψ : SpaceTime → ℝ} {Mψ : ℝ}
    (hJi : Integrable J) (hh : Integrable h) (hψi : Integrable ψ)
    (hψb : ∀ y, |ψ y| ≤ Mψ) :
    ∫ y, i3Psi2Smear J h y * ψ y = ∫ w, h w * ∫ y, J (w - y) * ψ y := by
  have hs := integrable_smear_prod hh hJi
  have hF : Integrable (fun p : SpaceTime × SpaceTime => h p.2 * J (p.2 - p.1) * ψ p.1)
      (volume.prod volume) := by
    refine hs.mul_bdd (c := Mψ) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hψi.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst)
    · rw [Real.norm_eq_abs]; exact hψb _
  have := integral_integral_swap (f := fun y w => h w * J (w - y) * ψ y) hF
  have e1 : ∀ y, ∫ w, h w * J (w - y) * ψ y = i3Psi2Smear J h y * ψ y := fun y => by
    unfold i3Psi2Smear
    rw [integral_mul_const]
  have e2 : ∀ w, ∫ y, h w * J (w - y) * ψ y = h w * ∫ y, J (w - y) * ψ y := fun w => by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  simp only [e1, e2] at this
  exact this

/-- `∫ smear h (y) J(p - y) dy = ∫ h(w) Q(w - p) dw`. -/
theorem integral_smear_mul_J {J Q h : SpaceTime → ℝ} {M : ℝ}
    (hJb : ∀ x, |J x| ≤ M) (hJi : Integrable J) (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (hh : Integrable h) (p : SpaceTime) :
    ∫ y, i3Psi2Smear J h y * J (p - y) = ∫ w, h w * Q (w - p) := by
  rw [integral_smear_mul hJi hh (integrable_comp_sub_left_spaceTime hJi p)
    (fun y => hJb _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [integral_J_mul_J hQJ]

/-- `∫ smear h₁ · smear h₂ = ∫ h₁(w) ∫ h₂(w') Q(w - w') dw' dw`. -/
theorem integral_smear_mul_smear {J Q h₁ h₂ : SpaceTime → ℝ} {M : ℝ} (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hJi : Integrable J) (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (hh₁ : Integrable h₁) (hh₂ : Integrable h₂) :
    ∫ y, i3Psi2Smear J h₁ y * i3Psi2Smear J h₂ y = ∫ w, h₁ w * ∫ w', h₂ w' * Q (w - w') := by
  rw [integral_smear_mul hJi hh₁ (integrable_i3Psi2Smear hh₂ hJi)
    (fun y => abs_i3Psi2Smear_le hJm hJb hh₂ y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  congr 1
  have h1 := integral_smear_mul_J hJb hJi hQJ hh₂ w
  have e : ∀ w' : SpaceTime, Q (w - w') = Q (w' - w) := fun w' => by
    rw [← neg_sub w' w]
    exact (i3Psi2_Q_neg hQJ _)
  calc ∫ y, J (w - y) * i3Psi2Smear J h₂ y = ∫ y, i3Psi2Smear J h₂ y * J (w - y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce; ring
    _ = ∫ w', h₂ w' * Q (w' - w) := h1
    _ = _ := by simp only [e]

end RegularityStructures

end
