/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiPowers

/-!
# Integrable majorants with an explicit integral bound

`SingularIntLe f X` records that `f` is integrable on space-time with `∫ f ≤ X`.  Using it we
package the integral estimates of products of centred parabolic powers that are needed for the
diagram bounds of the tree `I(Ψ³)Ψ`:

* two powers of total order `5 + η > 5` (from `integrable_and_integral_singularPow_mul_le`);
* three powers of total order `5 + η`, two of which have total order `< 5`;
* two powers of total order `< 5`, restricted to the time slab `|t| ≤ 2`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14 and (10.37a).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- `f` is integrable on space-time with integral at most `X`. -/
def SingularIntLe (f : SpaceTime → ℝ) (X : ℝ) : Prop :=
  Integrable f ∧ ∫ w, f w ≤ X

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem SingularIntLe.add {f g : SpaceTime → ℝ} {X Y : ℝ} (hf : SingularIntLe f X)
    (hg : SingularIntLe g Y) : SingularIntLe (fun w => f w + g w) (X + Y) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1]; exact add_le_add hf.2 hg.2⟩

theorem SingularIntLe.const_mul {f : SpaceTime → ℝ} {X c : ℝ} (hf : SingularIntLe f X)
    (hc : 0 ≤ c) : SingularIntLe (fun w => c * f w) (c * X) :=
  ⟨hf.1.const_mul c, by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hf.2 hc⟩

theorem SingularIntLe.mono_right {f : SpaceTime → ℝ} {X Y : ℝ} (hf : SingularIntLe f X)
    (hXY : X ≤ Y) : SingularIntLe f Y :=
  ⟨hf.1, hf.2.trans hXY⟩

/-- A nonnegative measurable function dominated almost everywhere by `f` inherits the bound. -/
theorem SingularIntLe.of_le {f F : SpaceTime → ℝ} {X : ℝ} (hf : SingularIntLe f X)
    (hF : AEStronglyMeasurable F volume) (h0 : ∀ᵐ w : SpaceTime ∂volume, 0 ≤ F w)
    (h : ∀ᵐ w : SpaceTime ∂volume, F w ≤ f w) : SingularIntLe F X := by
  refine ⟨Integrable.mono' hf.1 hF ?_, (integral_mono_of_nonneg h0 hf.1 h).trans hf.2⟩
  filter_upwards [h0, h] with w h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

theorem singularIntLe_zero : SingularIntLe (fun _ => 0) 0 :=
  ⟨integrable_zero _ _ _, by simp⟩

/-- Two centred powers of total order `5 + η`, `η > 0`. -/
theorem singularIntLe_mul_two {a b η : ℝ} (ha : 0 < a) (ha5 : a < 5) (hb : 0 < b) (hb5 : b < 5)
    (hη : 0 < η) (hab : a + b = 5 + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : SpaceTime, 0 < torusParabolicSize (p - q) →
      SingularIntLe (fun w => singularPow a p w * singularPow b q w)
        (C * torusParabolicSize (p - q) ^ (-η)) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le ha ha5 hb hb5 (by linarith)
  refine ⟨C, hC, fun p q hpq => ?_⟩
  have e : 5 - a - b = -η := by linarith
  obtain ⟨h1, h2⟩ := h p q hpq
  rw [e] at h2
  exact ⟨h1, h2⟩

/-- Three centred powers of total order `5 + η`, the first two of total order `< 5`. -/
theorem singularIntLe_mul_three {a b c η : ℝ} (ha : 0 < a) (hb : 0 < b) (hab5 : a + b < 5)
    (hc : 0 < c) (hc5 : c < 5) (hη : 0 < η) (habc : a + b + c = 5 + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q r : SpaceTime, 0 < torusParabolicSize (p - r) →
      0 < torusParabolicSize (q - r) →
      SingularIntLe (fun w => singularPow a p w * singularPow b q w * singularPow c r w)
        (C * (torusParabolicSize (p - r) ^ (-η) + torusParabolicSize (q - r) ^ (-η))) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_two (a := a + b) (b := c) (η := η) (by linarith)
    hab5 hc hc5 hη habc
  refine ⟨C, hC, fun p q r hpr hqr => ?_⟩
  have h1 := h p r hpr
  have h2 := h q r hqr
  have := h1.add h2
  refine (this.mono_right (le_of_eq (by ring))).of_le ?_ ?_ ?_
  · exact (((measurable_singularPow a p).mul (measurable_singularPow b q)).mul
      (measurable_singularPow c r)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => mul_nonneg
      (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      (singularPow_nonneg _ _ _)
  · filter_upwards [ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos q]
      with w hp hq
    have := singularPow_mul_le (a := a) (b := b) ha.le hb.le hp hq
    calc singularPow a p w * singularPow b q w * singularPow c r w
        ≤ (singularPow (a + b) p w + singularPow (a + b) q w) * singularPow c r w :=
          mul_le_mul_of_nonneg_right this (singularPow_nonneg _ _ _)
      _ = _ := by ring

end RegularityStructures

end
