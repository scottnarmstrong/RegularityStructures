/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOnePotential

/-!
# Pairings of potentials `y ↦ ∫ h(w) |J(w - y)| dw`

Abstract Tonelli arguments: the integral of `u · Pot h` and of `Pot h₁ · Pot h₂` against `dy`
is bounded in terms of pointwise majorants which are certified by `SingularIntLe` statements.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The potential `y ↦ ∫ h(w) |J(w - y)| dw`. -/
def i3Psi2Pot (J h : SpaceTime → ℝ) (y : SpaceTime) : ℝ := ∫ w, h w * |J (w - y)|

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2Pot_nonneg {J h : SpaceTime → ℝ} (hh : ∀ w, 0 ≤ h w) (y : SpaceTime) :
    0 ≤ i3Psi2Pot J h y :=
  integral_nonneg fun w => mul_nonneg (hh w) (abs_nonneg _)

theorem measurable_abs_J_sub {J : SpaceTime → ℝ} (hJm : Measurable J) :
    Measurable (fun p : SpaceTime × SpaceTime => |J (p.1 - p.2)|) :=
  continuous_abs.measurable.comp (hJm.comp (measurable_fst.sub measurable_snd))

/-- `∫ u · Pot h ≤ X`, from a pointwise bound on `∫ u(y) |J(w - y)| dy`. -/
theorem integral_mul_pot_le {J h u H U : SpaceTime → ℝ} {X : ℝ} (hJm : Measurable J)
    (hu0 : ∀ y, 0 ≤ u y) (hum : Measurable u) (hh0 : ∀ w, 0 ≤ h w) (hhm : Measurable h)
    (hhH : ∀ᵐ w : SpaceTime ∂volume, h w ≤ H w)
    (hU : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun y => u y * |J (w - y)|) ∧
      ∫ y, u y * |J (w - y)| ≤ U w)
    (hX : SingularIntLe (fun w => H w * U w) X) :
    Integrable (fun y => u y * i3Psi2Pot J h y) ∧ ∫ y, u y * i3Psi2Pot J h y ≤ X := by
  let G : SpaceTime → SpaceTime → ℝ := fun w y => h w * (u y * |J (w - y)|)
  have hGm : Measurable (Function.uncurry G) := by
    have := measurable_abs_J_sub hJm
    unfold Function.uncurry G
    fun_prop
  have hG0 : ∀ w y, 0 ≤ G w y := fun w y =>
    mul_nonneg (hh0 w) (mul_nonneg (hu0 y) (abs_nonneg _))
  have hGi : ∀ᵐ w : SpaceTime ∂volume, Integrable (G w) := by
    filter_upwards [hU] with w hw
    exact hw.1.const_mul (h w)
  have hint : ∀ w, ∫ y, G w y = h w * ∫ y, u y * |J (w - y)| := fun w => by
    simp only [G]; rw [integral_const_mul]
  have hH : Integrable (fun w => ∫ y, G w y) := by
    refine Integrable.mono' hX.1 (hGm.aestronglyMeasurable.integral_prod_right') ?_
    filter_upwards [hU, hhH] with w hw hH'
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (hG0 w)), hint]
    have n0 : 0 ≤ ∫ y, u y * |J (w - y)| :=
      integral_nonneg fun y => mul_nonneg (hu0 y) (abs_nonneg _)
    exact mul_le_mul hH' hw.2 n0 ((hh0 w).trans hH')
  obtain ⟨_, hmarg, hswap⟩ := integral_swap_nonneg hGm.aestronglyMeasurable hG0 hGi hH
  have e : ∀ y, ∫ w, G w y = u y * i3Psi2Pot J h y := fun y => by
    simp only [G, i3Psi2Pot]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  simp_rw [e] at hmarg hswap
  refine ⟨hmarg, hswap.trans_le ?_⟩
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
    integral_nonneg (hG0 w)) hX.1 ?_) hX.2
  filter_upwards [hU, hhH] with w hw hH'
  rw [hint]
  have n0 : 0 ≤ ∫ y, u y * |J (w - y)| :=
    integral_nonneg fun y => mul_nonneg (hu0 y) (abs_nonneg _)
  exact mul_le_mul hH' hw.2 n0 ((hh0 w).trans hH')

theorem measurable_i3Psi2Pot {J h : SpaceTime → ℝ} (hJm : Measurable J) (hhm : Measurable h) :
    Measurable (i3Psi2Pot J h) := by
  have hm : Measurable (fun p : SpaceTime × SpaceTime => h p.2 * |J (p.2 - p.1)|) := by
    have := measurable_abs_J_sub hJm
    have h2 : Measurable (fun p : SpaceTime × SpaceTime => |J (p.2 - p.1)|) :=
      continuous_abs.measurable.comp (hJm.comp (measurable_snd.sub measurable_fst))
    exact (hhm.comp measurable_snd).mul h2
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

/-- `∫ Pot h₁ · Pot h₂ ≤ X`. -/
theorem integral_pot_mul_pot_le {J h₁ h₂ H₁ H₂ R : SpaceTime → ℝ} {Λ : SpaceTime → SpaceTime → ℝ}
    {X : ℝ} (hJm : Measurable J) (hh₁0 : ∀ w, 0 ≤ h₁ w) (hh₁m : Measurable h₁)
    (hh₂0 : ∀ w, 0 ≤ h₂ w) (hh₂m : Measurable h₂) (hh₁H : ∀ᵐ w : SpaceTime ∂volume, h₁ w ≤ H₁ w)
    (hh₂H : ∀ᵐ w : SpaceTime ∂volume, h₂ w ≤ H₂ w)
    (hκ : ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
      Integrable (fun y => |J (w - y)| * |J (w' - y)|) ∧
        ∫ y, |J (w - y)| * |J (w' - y)| ≤ Λ w w')
    (hR : ∀ᵐ w' : SpaceTime ∂volume, SingularIntLe (fun w => H₁ w * Λ w w') (R w'))
    (hX : SingularIntLe (fun w' => H₂ w' * R w') X) :
    Integrable (fun y => i3Psi2Pot J h₁ y * i3Psi2Pot J h₂ y) ∧
      ∫ y, i3Psi2Pot J h₁ y * i3Psi2Pot J h₂ y ≤ X := by
  have hmeasJ : ∀ w' : SpaceTime, Measurable (fun y => |J (w' - y)|) := fun w' =>
    continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id))
  have step1 : ∀ᵐ w' : SpaceTime ∂volume, Integrable (fun y => |J (w' - y)| * i3Psi2Pot J h₁ y) ∧
      ∫ y, |J (w' - y)| * i3Psi2Pot J h₁ y ≤ R w' := by
    filter_upwards [hR] with w' hw'
    refine integral_mul_pot_le (U := fun w => Λ w w') hJm (fun y => abs_nonneg _) (hmeasJ w')
      hh₁0 hh₁m hh₁H ?_ hw'
    filter_upwards [ae_torusParabolicSize_sub_pos w'] with w hw
    have := hκ w w' (torusParabolicSize_sub_pos_symm hw)
    exact ⟨by simpa [mul_comm] using this.1, by simpa [mul_comm] using this.2⟩
  have step2 : ∀ᵐ w' : SpaceTime ∂volume, Integrable (fun y => i3Psi2Pot J h₁ y * |J (w' - y)|) ∧
      ∫ y, i3Psi2Pot J h₁ y * |J (w' - y)| ≤ R w' := by
    filter_upwards [step1] with w' hw'
    exact ⟨by simpa [mul_comm] using hw'.1, by simpa [mul_comm] using hw'.2⟩
  exact integral_mul_pot_le hJm (i3Psi2Pot_nonneg hh₁0) (measurable_i3Psi2Pot hJm hh₁m) hh₂0 hh₂m
    hh₂H step2 hX

end RegularityStructures

end
