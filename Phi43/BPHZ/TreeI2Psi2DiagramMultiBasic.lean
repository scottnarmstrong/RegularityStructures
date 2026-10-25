/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramBound
public import Phi43.BPHZ.TreeI2Psi2DiagramInner

/-!
# The tree `I(Ψ²) Ψ²`: building blocks with general exponents

Generalisations of `i2Psi2LintBound_kernel_sub_two` and `i2Psi2LintBound_kernel_sub_three` to
arbitrary exponents of the singular weights, for the difference bound (10.3).  With
`A(w) = K(y - w) - K(x - w)`, `r = s(y - x)`, the Hölder gain `γ ∈ [0, 1]` and exponents `e`,
`e₁`, `e₂`:

* `i2Psi2LintBound_kernel_sub_single`:
  `∫ |A| s(g - w)^(-e) ≲ B r^γ (s(y - g)^(-(γ+e-2)) + s(x - g)^(-(γ+e-2)))`;
* `i2Psi2LintBound_kernel_sub_pair`:
  `∫ |A| s(g₁ - w)^(-e₁) s(g₂ - w)^(-e₂) ≲ B r^γ (s(y - g₂)^(-η) + s(x - g₂)^(-η) +
  2 s(g₁ - g₂)^(-η))`, `η = γ + e₁ + e₂ - 2`.

The kernel hypotheses are bundled in `i2Psi2KernelHyp`.  [Hai14, Lemma 10.14, Lemma 10.18].
-/

@[expose] public section

namespace RegularityStructures

/-- The hypotheses on the kernel `K` of the diagram estimates: `0 ≤ B`, measurable, supported in
`|t| ≤ 1`, `|K| ≤ B s^(-3)` and `|K(u + h) - K u| ≤ B s(h) s(u)^(-4)` for `s(h) ≤ s(u)/2`. -/
def i2Psi2KernelHyp (K : SpaceTime → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ Measurable K ∧ (∀ u : SpaceTime, 1 < |u.1| → K u = 0) ∧
    (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) ∧
    (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

private theorem measurable_weight_mul' (p g : SpaceTime) (a b : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  (measurable_torusParabolicSize_sub_rpow p a).mul (measurable_torusParabolicSize_sub_rpow g b)

private theorem weight_mul_nonneg' (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- **Increment of `K` against `s(g - w)^(-e)`**, general exponent, `γ ∈ [0, 1]`, `γ + e > 2`. -/
theorem i2Psi2LintBound_kernel_sub_single {γ e : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (he5 : e < 5)
    (hγe : 2 < γ + e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y g : SpaceTime, 0 < torusParabolicSize (y - g) → 0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          torusParabolicSize (g - w) ^ (-e))
          (C * B * torusParabolicSize (y - x) ^ γ *
            (torusParabolicSize (y - g) ^ (-(γ + e - 2)) +
              torusParabolicSize (x - g) ^ (-(γ + e - 2)))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3 + γ) (b := e)
    (by linarith) (by linarith) (by linarith) he5 (by linarith)
  refine ⟨12 * CG, by positivity, ?_⟩
  intro K B hK x y g hyg hxg
  obtain ⟨hB, -, -, hKb, hKi⟩ := hK
  have e0 : (5 : ℝ) - (3 + γ) - e = -(γ + e - 2) := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e0] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-(3 + γ)) *
      torusParabolicSize (g - w) ^ (-e)) (measurable_weight_mul' y g _ _).aemeasurable
    (weight_mul_nonneg' y g _ _) (weight_mul_nonneg' x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) gx
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ γ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := abs_kernel_sub_le hB hγ0 hγ1 hKb hKi (x := x) (y := y) (w := w) hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-e) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  calc |K (y - w) - K (x - w)| * torusParabolicSize (g - w) ^ (-e)
      ≤ (12 * B * torusParabolicSize (y - x) ^ γ * (torusParabolicSize (y - w) ^ (-(3 + γ)) +
        torusParabolicSize (x - w) ^ (-(3 + γ)))) * torusParabolicSize (g - w) ^ (-e) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring

/-- **Increment of `K` against `s(g₁ - w)^(-e₁) s(g₂ - w)^(-e₂)`**, general exponents. -/
theorem i2Psi2LintBound_kernel_sub_pair {γ e₁ e₂ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (he₁ : 0 ≤ e₁) (he₂ : 0 < e₂) (h5 : 3 + γ + e₁ < 5) (he₂5 : e₂ < 5)
    (hsum : 2 < γ + e₁ + e₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y g₁ g₂ : SpaceTime, 0 < torusParabolicSize (y - g₂) →
        0 < torusParabolicSize (x - g₂) → 0 < torusParabolicSize (g₁ - g₂) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-e₁) * torusParabolicSize (g₂ - w) ^ (-e₂)))
          (C * B * torusParabolicSize (y - x) ^ γ *
            (torusParabolicSize (y - g₂) ^ (-(γ + e₁ + e₂ - 2)) +
              torusParabolicSize (x - g₂) ^ (-(γ + e₁ + e₂ - 2)) +
              2 * torusParabolicSize (g₁ - g₂) ^ (-(γ + e₁ + e₂ - 2)))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3 + γ + e₁) (b := e₂)
    (by linarith) h5 he₂ he₂5 (by linarith)
  refine ⟨12 * CG, by positivity, ?_⟩
  intro K B hK x y g₁ g₂ hy hx hg
  obtain ⟨hB, -, -, hKb, hKi⟩ := hK
  have e0 : (5 : ℝ) - (3 + γ + e₁) - e₂ = -(γ + e₁ + e₂ - 2) := by ring
  have gy := hG y g₂ hy
  have gx := hG x g₂ hx
  have gg := hG g₁ g₂ hg
  rw [e0] at gy gx gg
  have gg2 := gg.const_mul (c := 2) (by norm_num)
  have s := gy.add_three (g := fun w => torusParabolicSize (x - w) ^ (-(3 + γ + e₁)) *
      torusParabolicSize (g₂ - w) ^ (-e₂))
    (h := fun w => 2 * (torusParabolicSize (g₁ - w) ^ (-(3 + γ + e₁)) *
      torusParabolicSize (g₂ - w) ^ (-e₂))) (measurable_weight_mul' y g₂ _ _)
    (measurable_weight_mul' x g₂ _ _) (weight_mul_nonneg' y g₂ _ _) (weight_mul_nonneg' x g₂ _ _)
    (fun w => mul_nonneg (by norm_num) (weight_mul_nonneg' g₁ g₂ _ _ w))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg (by norm_num) (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
    gx gg2
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ γ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
    ae_torusParabolicSize_sub_pos g₁, ae_torusParabolicSize_sub_pos g₂] with w hyw hxw hgw hg2
  have h := abs_kernel_sub_le hB hγ0 hγ1 hKb hKi (x := x) (y := y) (w := w) hyw hxw
  have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-e₁) * torusParabolicSize (g₂ - w) ^ (-e₂) :=
    weight_mul_nonneg' g₁ g₂ _ _ w
  have py := torusParabolicSize_rpow_neg_mul_le (a := 3 + γ) (b := e₁) (by linarith) he₁
    hyw hgw
  have px := torusParabolicSize_rpow_neg_mul_le (a := 3 + γ) (b := e₁) (by linarith) he₁
    hxw hgw
  have e2 : (3 + γ) + e₁ = 3 + γ + e₁ := rfl
  have n3 : 0 ≤ torusParabolicSize (g₂ - w) ^ (-e₂) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have py' := mul_le_mul_of_nonneg_right py n3
  have px' := mul_le_mul_of_nonneg_right px n3
  calc |K (y - w) - K (x - w)| * (torusParabolicSize (g₁ - w) ^ (-e₁) *
          torusParabolicSize (g₂ - w) ^ (-e₂))
      ≤ (12 * B * torusParabolicSize (y - x) ^ γ * (torusParabolicSize (y - w) ^ (-(3 + γ)) +
        torusParabolicSize (x - w) ^ (-(3 + γ)))) * (torusParabolicSize (g₁ - w) ^ (-e₁) *
          torusParabolicSize (g₂ - w) ^ (-e₂)) := mul_le_mul_of_nonneg_right h n2
    _ = 12 * B * torusParabolicSize (y - x) ^ γ *
        (torusParabolicSize (y - w) ^ (-(3 + γ)) * torusParabolicSize (g₁ - w) ^ (-e₁) *
            torusParabolicSize (g₂ - w) ^ (-e₂) +
          torusParabolicSize (x - w) ^ (-(3 + γ)) * torusParabolicSize (g₁ - w) ^ (-e₁) *
            torusParabolicSize (g₂ - w) ^ (-e₂)) := by ring
    _ ≤ 12 * B * torusParabolicSize (y - x) ^ γ *
        ((torusParabolicSize (y - w) ^ (-(3 + γ + e₁)) +
            torusParabolicSize (g₁ - w) ^ (-(3 + γ + e₁))) * torusParabolicSize (g₂ - w) ^ (-e₂) +
          (torusParabolicSize (x - w) ^ (-(3 + γ + e₁)) +
            torusParabolicSize (g₁ - w) ^ (-(3 + γ + e₁))) * torusParabolicSize (g₂ - w) ^ (-e₂)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        exact add_le_add py' px'
    _ = _ := by ring

end RegularityStructures

end
