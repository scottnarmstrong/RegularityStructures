/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Point

/-!
# Global pointwise domination of the weights of `N₁`, `N₂` (difference of `I(Ψ³)Ψ²`)

Global versions of `abs_dK_dK_N1_le`, `abs_dK_dK_N2_le`: the slab is `|w.1| ≤ |z.1| + 1`,
`|v.1| ≤ |z'.1| + 1`, and the loss `3^δ` is replaced by `D^δ`, where `D` bounds the distance
that carries the loss on the slab.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Pointwise domination of the weight of `N₁`, global.** -/
theorem abs_dK_dK_N1_le_global {K : SpaceTime → ℝ} {B δ x₁ x₂ x₃ D : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hx₁ : 0 ≤ x₁) (hD0 : 0 ≤ D)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' w v : SpaceTime}
    (hD : ∀ w : SpaceTime, |w.1| ≤ |z.1| + 1 → torusParabolicSize (z' - w) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v)) :
    |i3Psi2dK K z w| * |i3Psi2dK K z' v| *
        (torusParabolicSize (w - z') ^ (-(2 + x₁)) * torusParabolicSize (w - v) ^ (-(1 + x₂)) *
          torusParabolicSize (z - v) ^ (-(2 + x₃))) ≤
      (B ^ 2 * (2 ^ (2 + x₁) * D ^ δ)) *
        i3Psi2N1Majorant (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have n2 : (0 : ℝ) ≤ 2 ^ (2 + x₁) := Real.rpow_nonneg (by norm_num) _
  have hrhs := i3Psi2N1Majorant_nonneg (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v
  have hrhs' : 0 ≤ (B ^ 2 * (2 ^ (2 + x₁) * D ^ δ)) *
      i3Psi2N1Majorant (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v :=
    mul_nonneg (mul_nonneg (sq_nonneg B) (mul_nonneg n2 n3)) hrhs
  by_cases hw : |w.1| ≤ |z.1| + 1
  · by_cases hv : |v.1| ≤ |z'.1| + 1
    · have a1 := abs_dK_le hK h1 h0
      have a2 := abs_dK_le hK h1' h0'
      have c1 : torusParabolicSize (w - z') ^ (-(2 + x₁)) ≤
          2 ^ (2 + x₁) * (D ^ δ * singularPow (2 + (x₁ + δ)) z' w) := by
        have f := rpow_neg_flip_singularPow (p := 2 + x₁) (by linarith) hz'w
        have l := singularPow_loss_le_of_le (p := 2 + x₁) hδ hz'w (hD w hw)
        have e : 2 + x₁ + δ = 2 + (x₁ + δ) := by ring
        rw [e] at l
        exact f.trans (mul_le_mul_of_nonneg_left l (Real.rpow_nonneg (by norm_num) _))
      have nA : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have nB : 0 ≤ B * (singularPow 3 z' v + singularPow 3 0 v) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have nW1 : 0 ≤ torusParabolicSize (w - z') ^ (-(2 + x₁)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW2 : 0 ≤ torusParabolicSize (w - v) ^ (-(1 + x₂)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW3 : 0 ≤ torusParabolicSize (z - v) ^ (-(2 + x₃)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have key : |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
          (torusParabolicSize (w - z') ^ (-(2 + x₁)) * torusParabolicSize (w - v) ^ (-(1 + x₂)) *
            torusParabolicSize (z - v) ^ (-(2 + x₃))) ≤
          ((B * (singularPow 3 z w + singularPow 3 0 w)) *
            (B * (singularPow 3 z' v + singularPow 3 0 v))) *
          ((2 ^ (2 + x₁) * (D ^ δ * singularPow (2 + (x₁ + δ)) z' w)) *
            torusParabolicSize (w - v) ^ (-(1 + x₂)) * torusParabolicSize (z - v) ^ (-(2 + x₃))) :=
        mul_le_mul (mul_le_mul a1 a2 (abs_nonneg _) nA)
          (mul_le_mul (mul_le_mul c1 le_rfl nW2 (mul_nonneg n2 (mul_nonneg n3
            (singularPow_nonneg _ _ _)))) le_rfl nW3
            (mul_nonneg (mul_nonneg n2 (mul_nonneg n3 (singularPow_nonneg _ _ _))) nW2))
          (mul_nonneg (mul_nonneg nW1 nW2) nW3) (mul_nonneg nA nB)
      refine key.trans (le_of_eq ?_)
      unfold i3Psi2N1Majorant singularPow
      ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
      unfold i3Psi2dK
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
    unfold i3Psi2dK
    rw [this, abs_zero]
    simpa using hrhs'

/-- **Pointwise domination of the weight of `N₂`, global.** -/
theorem abs_dK_dK_N2_le_global {K : SpaceTime → ℝ} {B δ y₁ y₂ y₃ y₄ y₅ D : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₄ : 0 ≤ y₄) (hD0 : 0 ≤ D)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' w v : SpaceTime}
    (hD : ∀ w : SpaceTime, |w.1| ≤ |z.1| + 1 → torusParabolicSize (z - w) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v)) :
    |i3Psi2dK K z w| * |i3Psi2dK K z' v| *
        (torusParabolicSize (w - z) ^ (-(1 + y₁)) * torusParabolicSize (w - z') ^ (-(1 + y₂)) *
          torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (v - z') ^ (-(1 + y₄)) *
          torusParabolicSize (z - v) ^ (-(1 + y₅))) ≤
      (B ^ 2 * (2 ^ (1 + y₁) * D ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄))) *
        i3Psi2N2Majorant (y₁ + δ) y₂ y₃ y₄ y₅ z z' w v := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have n21 : (0 : ℝ) ≤ 2 ^ (1 + y₁) := Real.rpow_nonneg (by norm_num) _
  have n22 : (0 : ℝ) ≤ 2 ^ (1 + y₂) := Real.rpow_nonneg (by norm_num) _
  have n24 : (0 : ℝ) ≤ 2 ^ (1 + y₄) := Real.rpow_nonneg (by norm_num) _
  have hrhs := i3Psi2N2Majorant_nonneg (y₁ + δ) y₂ y₃ y₄ y₅ z z' w v
  have hc : 0 ≤ B ^ 2 * (2 ^ (1 + y₁) * D ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄)) :=
    mul_nonneg (sq_nonneg B) (mul_nonneg (mul_nonneg (mul_nonneg n21 n3) n22) n24)
  have hrhs' := mul_nonneg hc hrhs
  by_cases hw : |w.1| ≤ |z.1| + 1
  · by_cases hv : |v.1| ≤ |z'.1| + 1
    · have a1 := abs_dK_le hK h1 h0
      have a2 := abs_dK_le hK h1' h0'
      have c1 : torusParabolicSize (w - z) ^ (-(1 + y₁)) ≤
          2 ^ (1 + y₁) * (D ^ δ * singularPow (1 + (y₁ + δ)) z w) := by
        have f := rpow_neg_flip_singularPow (p := 1 + y₁) (by linarith) h1
        have l := singularPow_loss_le_of_le (p := 1 + y₁) hδ h1 (hD w hw)
        have e : 1 + y₁ + δ = 1 + (y₁ + δ) := by ring
        rw [e] at l
        exact f.trans (mul_le_mul_of_nonneg_left l n21)
      have c2 : torusParabolicSize (w - z') ^ (-(1 + y₂)) ≤
          2 ^ (1 + y₂) * singularPow (1 + y₂) z' w :=
        rpow_neg_flip_singularPow (p := 1 + y₂) (by linarith) hz'w
      have c4 : torusParabolicSize (v - z') ^ (-(1 + y₄)) ≤
          2 ^ (1 + y₄) * singularPow (1 + y₄) z' v :=
        rpow_neg_flip_singularPow (p := 1 + y₄) (by linarith) h1'
      have e1 := singularPow_mul_le (a := 3) (b := 1 + y₄) (by norm_num) (by linarith) h1' h1'
      have e2 := singularPow_mul_le (a := 3) (b := 1 + y₄) (by norm_num) (by linarith) h0' h1'
      have e : (3 : ℝ) + (1 + y₄) = 4 + y₄ := by ring
      rw [e] at e1 e2
      have nS3 : 0 ≤ singularPow 3 z' v + singularPow 3 0 v :=
        add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
      have nS4 := singularPow_nonneg (1 + y₄) z' v
      have hR : |K (z' - v) - K (-v)| * torusParabolicSize (v - z') ^ (-(1 + y₄)) ≤
          B * (2 ^ (1 + y₄) * (3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v)) := by
        have h5 : (singularPow 3 z' v + singularPow 3 0 v) * singularPow (1 + y₄) z' v ≤
            3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v := by
          have := add_le_add e1 e2
          nlinarith [this]
        calc |K (z' - v) - K (-v)| * torusParabolicSize (v - z') ^ (-(1 + y₄))
            ≤ (B * (singularPow 3 z' v + singularPow 3 0 v)) *
                (2 ^ (1 + y₄) * singularPow (1 + y₄) z' v) :=
              mul_le_mul a2 c4 (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
                (mul_nonneg hB nS3)
          _ = B * (2 ^ (1 + y₄) * ((singularPow 3 z' v + singularPow 3 0 v) *
                singularPow (1 + y₄) z' v)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 n24) hB
      have nA : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have nW1 : 0 ≤ torusParabolicSize (w - z) ^ (-(1 + y₁)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW2 : 0 ≤ torusParabolicSize (w - z') ^ (-(1 + y₂)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW3 : 0 ≤ torusParabolicSize (w - v) ^ (-(1 + y₃)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW4 : 0 ≤ torusParabolicSize (v - z') ^ (-(1 + y₄)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nW5 : 0 ≤ torusParabolicSize (z - v) ^ (-(1 + y₅)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have nS1 := singularPow_nonneg (1 + (y₁ + δ)) z w
      have nS2 := singularPow_nonneg (1 + y₂) z' w
      have nR : 0 ≤ B * (2 ^ (1 + y₄) * (3 * singularPow (4 + y₄) z' v +
          singularPow (4 + y₄) 0 v)) :=
        mul_nonneg hB (mul_nonneg n24 (add_nonneg (mul_nonneg (by norm_num)
          (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _)))
      have hL : |K (z - w) - K (-w)| * (torusParabolicSize (w - z) ^ (-(1 + y₁)) *
            torusParabolicSize (w - z') ^ (-(1 + y₂))) ≤
          (B * (singularPow 3 z w + singularPow 3 0 w)) *
            ((2 ^ (1 + y₁) * (D ^ δ * singularPow (1 + (y₁ + δ)) z w)) *
              (2 ^ (1 + y₂) * singularPow (1 + y₂) z' w)) :=
        mul_le_mul a1 (mul_le_mul c1 c2 nW2 (mul_nonneg n21 (mul_nonneg n3 nS1))) (mul_nonneg nW1
          nW2) nA
      have key : (|K (z - w) - K (-w)| * (torusParabolicSize (w - z) ^ (-(1 + y₁)) *
            torusParabolicSize (w - z') ^ (-(1 + y₂)))) *
          ((|K (z' - v) - K (-v)| * torusParabolicSize (v - z') ^ (-(1 + y₄))) *
            (torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (z - v) ^ (-(1 + y₅)))) ≤
          ((B * (singularPow 3 z w + singularPow 3 0 w)) *
            ((2 ^ (1 + y₁) * (D ^ δ * singularPow (1 + (y₁ + δ)) z w)) *
              (2 ^ (1 + y₂) * singularPow (1 + y₂) z' w))) *
          ((B * (2 ^ (1 + y₄) * (3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v))) *
            (torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (z - v) ^ (-(1 + y₅)))) :=
        mul_le_mul hL (mul_le_mul hR le_rfl (mul_nonneg nW3 nW5) nR)
          (mul_nonneg (mul_nonneg (abs_nonneg _) nW4) (mul_nonneg nW3 nW5))
          (mul_nonneg nA (mul_nonneg (mul_nonneg n21 (mul_nonneg n3 nS1))
            (mul_nonneg n22 nS2)))
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
      · unfold i3Psi2dK; ring
      · unfold i3Psi2N2Majorant singularPow
        ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
      unfold i3Psi2dK
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
    unfold i3Psi2dK
    rw [this, abs_zero]
    simpa using hrhs'

end RegularityStructures

end
