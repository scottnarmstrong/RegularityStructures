/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Integral of a product of two differences

If `F = (a - b)(a' - b')` with `|a| ≤ ua`, `|b| ≤ ub`, `|a'| ≤ ua'`, `|b'| ≤ ub'` and the four
products `ua ua'`, `ua ub'`, `ub ua'`, `ub ub'` are integrable with integrals at most
`I₁, …, I₄`, then `F` is integrable and `|∫ F| ≤ I₁ + I₂ + I₃ + I₄`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem integrable_and_abs_integral_le_of_parts {F a a' b b' ua ua' ub ub' : SpaceTime → ℝ}
    {I₁ I₂ I₃ I₄ : ℝ} (hF : ∀ y, F y = (a y - b y) * (a' y - b' y))
    (hm : AEStronglyMeasurable F volume)
    (ha : ∀ᵐ y : SpaceTime ∂volume, |a y| ≤ ua y) (ha' : ∀ᵐ y : SpaceTime ∂volume, |a' y| ≤ ua' y)
    (hb : ∀ᵐ y : SpaceTime ∂volume, |b y| ≤ ub y) (hb' : ∀ᵐ y : SpaceTime ∂volume, |b' y| ≤ ub' y)
    (i₁ : Integrable (fun y => ua y * ua' y)) (b₁ : ∫ y, ua y * ua' y ≤ I₁)
    (i₂ : Integrable (fun y => ua y * ub' y)) (b₂ : ∫ y, ua y * ub' y ≤ I₂)
    (i₃ : Integrable (fun y => ub y * ua' y)) (b₃ : ∫ y, ub y * ua' y ≤ I₃)
    (i₄ : Integrable (fun y => ub y * ub' y)) (b₄ : ∫ y, ub y * ub' y ≤ I₄) :
    Integrable F ∧ |∫ y, F y| ≤ I₁ + I₂ + I₃ + I₄ := by
  have hMaj : Integrable (fun y => ua y * ua' y + ua y * ub' y + ub y * ua' y + ub y * ub' y) :=
    ((i₁.add i₂).add i₃).add i₄
  have hle : ∀ᵐ y : SpaceTime ∂volume, ‖F y‖ ≤
      ua y * ua' y + ua y * ub' y + ub y * ua' y + ub y * ub' y := by
    filter_upwards [ha, ha', hb, hb'] with y h1 h2 h3 h4
    rw [Real.norm_eq_abs, hF, abs_mul]
    have e1 : |a y - b y| ≤ ua y + ub y := (abs_sub _ _).trans (add_le_add h1 h3)
    have e2 : |a' y - b' y| ≤ ua' y + ub' y := (abs_sub _ _).trans (add_le_add h2 h4)
    calc |a y - b y| * |a' y - b' y| ≤ (ua y + ub y) * (ua' y + ub' y) :=
          mul_le_mul e1 e2 (abs_nonneg _) ((abs_nonneg _).trans e1)
      _ = _ := by ring
  have hint : Integrable F := Integrable.mono' hMaj hm hle
  refine ⟨hint, ?_⟩
  have := norm_integral_le_of_norm_le hMaj hle
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have j12 : Integrable (fun y => ua y * ua' y + ua y * ub' y) := i₁.add i₂
  have j123 : Integrable (fun y => ua y * ua' y + ua y * ub' y + ub y * ua' y) := j12.add i₃
  rw [integral_add j123 i₄, integral_add j12 i₃, integral_add i₁ i₂]
  linarith

end RegularityStructures

end
