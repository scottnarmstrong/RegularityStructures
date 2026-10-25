/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramKernel

/-!
# Integrals of the kernel increment against singular weights

With `A(w) = K(y - w) - K(x - w)` and `r = s(y - x)`:

* `i2Psi2LintBound_kernel_sub_two`: `∫ |A(w)| s(g - w)^(-2) dw ≲ B r^θ (s(y - g)^(-θ) + s(x - g)^(-θ))`
  for `θ ∈ (0, 1]`;
* `i2Psi2LintBound_kernel_sub_three`: `∫ |A(w)| s(g₁ - w)^(-1) s(g₂ - w)^(-κ) dw ≲
  B r^θ (s(y - g₂)^(-(θ+κ-1)) + s(x - g₂)^(-(θ+κ-1)) + 2 s(g₁ - g₂)^(-(θ+κ-1)))` for
  `θ ∈ [0, 1)` and `θ + κ > 1`;
* `i2Psi2LintBound_kernel_sub_slab`: `∫ |A(w)| s(g₁ - w)^(-λ₁) s(g₂ - w)^(-λ₂) dw ≲ B r^θ` when
  `3 + θ + λ₁ + λ₂ < 5` (no singular output), under the support hypotheses.

The constants depend only on the exponents.  [Hai14, Lemma 10.14, Lemma 10.18].
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem measurable_weight_mul (p g : SpaceTime) (a b : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  (measurable_torusParabolicSize_sub_rpow p a).mul (measurable_torusParabolicSize_sub_rpow g b)

private theorem weight_mul_nonneg (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- **Increment of `K` against `s(g - w)^(-2)`**, [Hai14, Lemma 10.14 and 10.18]. -/
theorem i2Psi2LintBound_kernel_sub_two {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g : SpaceTime, 0 < torusParabolicSize (y - g) → 0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          torusParabolicSize (g - w) ^ (-(2 : ℝ)))
          (C * B * torusParabolicSize (y - x) ^ θ *
            (torusParabolicSize (y - g) ^ (-θ) + torusParabolicSize (x - g) ^ (-θ))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3 + θ) (b := 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith)
  refine ⟨12 * CG, by positivity, ?_⟩
  intro K B hB hKb hKi x y g hyg hxg
  have e : (5 : ℝ) - (3 + θ) - 2 = -θ := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-(3 + θ)) *
      torusParabolicSize (g - w) ^ (-(2 : ℝ))) (measurable_weight_mul y g _ _).aemeasurable
    (weight_mul_nonneg y g _ _) (weight_mul_nonneg x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) gx
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ θ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := abs_kernel_sub_le hB hθ.le hθ1 hKb hKi (x := x) (y := y) (w := w) hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  calc |K (y - w) - K (x - w)| * torusParabolicSize (g - w) ^ (-(2 : ℝ))
      ≤ (12 * B * torusParabolicSize (y - x) ^ θ * (torusParabolicSize (y - w) ^ (-(3 + θ)) +
        torusParabolicSize (x - w) ^ (-(3 + θ)))) * torusParabolicSize (g - w) ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring

/-- **Increment of `K` against `s(g₁ - w)^(-1) s(g₂ - w)^(-κ)`**, `θ ∈ [0, 1)`, `θ + κ > 1`. -/
theorem i2Psi2LintBound_kernel_sub_three {θ κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hκ5 : κ < 5) (hθκ : 1 < θ + κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g₁ g₂ : SpaceTime, 0 < torusParabolicSize (y - g₂) →
        0 < torusParabolicSize (x - g₂) → 0 < torusParabolicSize (g₁ - g₂) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) * torusParabolicSize (g₂ - w) ^ (-κ)))
          (C * B * torusParabolicSize (y - x) ^ θ *
            (torusParabolicSize (y - g₂) ^ (-(θ + κ - 1)) +
              torusParabolicSize (x - g₂) ^ (-(θ + κ - 1)) +
              2 * torusParabolicSize (g₁ - g₂) ^ (-(θ + κ - 1)))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 4 + θ) (b := κ)
    (by linarith) (by linarith) hκ hκ5 (by linarith)
  refine ⟨12 * CG, by positivity, ?_⟩
  intro K B hB hKb hKi x y g₁ g₂ hy hx hg
  have e : (5 : ℝ) - (4 + θ) - κ = -(θ + κ - 1) := by ring
  have gy := hG y g₂ hy
  have gx := hG x g₂ hx
  have gg := hG g₁ g₂ hg
  rw [e] at gy gx gg
  have gg2 := gg.const_mul (c := 2) (by norm_num)
  have s := gy.add_three (g := fun w => torusParabolicSize (x - w) ^ (-(4 + θ)) *
      torusParabolicSize (g₂ - w) ^ (-κ))
    (h := fun w => 2 * (torusParabolicSize (g₁ - w) ^ (-(4 + θ)) *
      torusParabolicSize (g₂ - w) ^ (-κ))) (measurable_weight_mul y g₂ _ _)
    (measurable_weight_mul x g₂ _ _) (weight_mul_nonneg y g₂ _ _) (weight_mul_nonneg x g₂ _ _)
    (fun w => mul_nonneg (by norm_num) (weight_mul_nonneg g₁ g₂ _ _ w))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg (by norm_num) (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
    gx gg2
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ θ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
    ae_torusParabolicSize_sub_pos g₁, ae_torusParabolicSize_sub_pos g₂] with w hyw hxw hgw hg2
  have h := abs_kernel_sub_le hB hθ0 hθ1.le hKb hKi (x := x) (y := y) (w := w) hyw hxw
  have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) * torusParabolicSize (g₂ - w) ^ (-κ) :=
    weight_mul_nonneg g₁ g₂ _ _ w
  have py := torusParabolicSize_rpow_neg_mul_le (a := 3 + θ) (b := 1) (by linarith) (by norm_num)
    hyw hgw
  have px := torusParabolicSize_rpow_neg_mul_le (a := 3 + θ) (b := 1) (by linarith) (by norm_num)
    hxw hgw
  have e2 : (3 + θ) + 1 = 4 + θ := by ring
  rw [e2] at py px
  have n3 : 0 ≤ torusParabolicSize (g₂ - w) ^ (-κ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have py' := mul_le_mul_of_nonneg_right py n3
  have px' := mul_le_mul_of_nonneg_right px n3
  calc |K (y - w) - K (x - w)| * (torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
          torusParabolicSize (g₂ - w) ^ (-κ))
      ≤ (12 * B * torusParabolicSize (y - x) ^ θ * (torusParabolicSize (y - w) ^ (-(3 + θ)) +
        torusParabolicSize (x - w) ^ (-(3 + θ)))) * (torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
          torusParabolicSize (g₂ - w) ^ (-κ)) := mul_le_mul_of_nonneg_right h n2
    _ = 12 * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
            torusParabolicSize (g₂ - w) ^ (-κ) +
          torusParabolicSize (x - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
            torusParabolicSize (g₂ - w) ^ (-κ)) := by ring
    _ ≤ 12 * B * torusParabolicSize (y - x) ^ θ *
        ((torusParabolicSize (y - w) ^ (-(4 + θ)) + torusParabolicSize (g₁ - w) ^ (-(4 + θ))) *
            torusParabolicSize (g₂ - w) ^ (-κ) +
          (torusParabolicSize (x - w) ^ (-(4 + θ)) + torusParabolicSize (g₁ - w) ^ (-(4 + θ))) *
            torusParabolicSize (g₂ - w) ^ (-κ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        exact add_le_add py' px'
    _ = _ := by ring

/-- **Increment of `K` against two singular weights, bounded case.** -/
theorem i2Psi2LintBound_kernel_sub_slab {θ l₁ l₂ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (he : 3 + θ + l₁ + l₂ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g₁ g₂ : SpaceTime, |y.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 → |g₂.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)))
          (C * B * torusParabolicSize (y - x) ^ θ) := by
  obtain ⟨CT, hCT, hT⟩ := i2Psi2LintBound_slab_triple (l₁ := 3 + θ) (l₂ := l₁) (l₃ := l₂)
    (by linarith) hl₁ hl₂ (by linarith) (by linarith)
  refine ⟨24 * CT, by positivity, ?_⟩
  intro K B hB hKs hKb hKi x y g₁ g₂ hxy hg₁ hg₂
  have hy2 : |y.1 - x.1| ≤ 2 := by linarith
  have hx2 : |x.1 - x.1| ≤ 2 := by simp
  have ty := hT x.1 y g₁ g₂ hy2 hg₁ hg₂
  have tx := hT x.1 x g₁ g₂ hx2 hg₁ hg₂
  have m : ∀ p : SpaceTime, Measurable fun w : SpaceTime => i2Psi2Slab x.1 w *
      (torusParabolicSize (p - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun p =>
    (measurable_i2Psi2Slab _).mul (((measurable_torusParabolicSize_sub_rpow p _).mul
      (measurable_torusParabolicSize_sub_rpow g₁ _)).mul
      (measurable_torusParabolicSize_sub_rpow g₂ _))
  have n : ∀ (p : SpaceTime) w, 0 ≤ i2Psi2Slab x.1 w *
      (torusParabolicSize (p - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun p w =>
    mul_nonneg (i2Psi2Slab_nonneg _ _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have s := ty.add (g := fun w => i2Psi2Slab x.1 w *
      (torusParabolicSize (x - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂))) (m y).aemeasurable (n y) (n x) hCT hCT tx
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ θ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hyw hxw
  have h := abs_kernel_sub_le_slab hB hθ0 hθ1 hKs hKb hKi hxy hyw hxw
  have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂) :=
    weight_mul_nonneg g₁ g₂ _ _ w
  calc |K (y - w) - K (x - w)| * (torusParabolicSize (g₁ - w) ^ (-l₁) *
          torusParabolicSize (g₂ - w) ^ (-l₂))
      ≤ (i2Psi2Slab x.1 w * (12 * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - w) ^ (-(3 + θ)) + torusParabolicSize (x - w) ^ (-(3 + θ))))) *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring

end RegularityStructures

end
