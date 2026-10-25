/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN1
public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# The weighted diagram `N₂` of `I(Ψ³)Ψ²` with general exponents

The diagram `N₂` (chaos `3`) is the double integral of `δK(z, w) δK(z', v)` against the weight
`s(w - z)^(-1) s(w - z')^(-1) s(w - v)^(-1) s(v - z')^(-1) s(z - v)^(-1)`.  Each of the five
exponents may be raised by a small `yᵢ ≥ 0` (the factor `μ s^(-θ)` of one covariance in the
difference of the fields), and the exponent of `s(w - z)` also carries the slab loss `δ`.  This file
contains the pointwise domination by the majorant `i3Psi2N2Majorant`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The majorant of the diagram `N₂`: exponents `1 + ν₁` at `(z, w)`, `1 + y₂` at `(z', w)`,
`1 + y₃` at `(w, v)`, `4 + y₄` at `(z', v)`, `(0, v)` and `1 + y₅` at `(z, v)`. -/
def i3Psi2N2Majorant (ν₁ y₂ y₃ y₄ y₅ : ℝ) (z z' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + ν₁) z w *
      singularPow (1 + y₂) z' w) *
    ((3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v *
      singularPow (1 + y₃) w v)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2N2Majorant_nonneg (ν₁ y₂ y₃ y₄ y₅ : ℝ) (z z' w v : SpaceTime) :
    0 ≤ i3Psi2N2Majorant ν₁ y₂ y₃ y₄ y₅ z z' w v := by
  unfold i3Psi2N2Majorant
  have := singularPow_nonneg
  exact mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg (this _ _ _) (this _ _ _)) (this _ _ _))
    (this _ _ _)) (mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) (this _ _ _))
    (this _ _ _)) (this _ _ _)) (this _ _ _))

/-- **Pointwise domination of the weight of `N₂`.** -/
theorem abs_dK_dK_N2_le {K : SpaceTime → ℝ} {B δ y₁ y₂ y₃ y₄ y₅ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₄ : 0 ≤ y₄)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v)) :
    |i3Psi2dK K z w| * |i3Psi2dK K z' v| *
        (torusParabolicSize (w - z) ^ (-(1 + y₁)) * torusParabolicSize (w - z') ^ (-(1 + y₂)) *
          torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (v - z') ^ (-(1 + y₄)) *
          torusParabolicSize (z - v) ^ (-(1 + y₅))) ≤
      (B ^ 2 * (2 ^ (1 + y₁) * 3 ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄))) *
        i3Psi2N2Majorant (y₁ + δ) y₂ y₃ y₄ y₅ z z' w v := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have n21 : (0 : ℝ) ≤ 2 ^ (1 + y₁) := Real.rpow_nonneg (by norm_num) _
  have n22 : (0 : ℝ) ≤ 2 ^ (1 + y₂) := Real.rpow_nonneg (by norm_num) _
  have n24 : (0 : ℝ) ≤ 2 ^ (1 + y₄) := Real.rpow_nonneg (by norm_num) _
  have hrhs := i3Psi2N2Majorant_nonneg (y₁ + δ) y₂ y₃ y₄ y₅ z z' w v
  have hc : 0 ≤ B ^ 2 * (2 ^ (1 + y₁) * 3 ^ δ * 2 ^ (1 + y₂) * 2 ^ (1 + y₄)) :=
    mul_nonneg (sq_nonneg B) (mul_nonneg (mul_nonneg (mul_nonneg n21 n3) n22) n24)
  have hrhs' := mul_nonneg hc hrhs
  by_cases hw : |w.1| ≤ 2
  · by_cases hv : |v.1| ≤ 2
    · have hz1t := abs_fst_le_one_of_size_le_one hz1
      have a1 := abs_dK_le hK h1 h0
      have a2 := abs_dK_le hK h1' h0'
      have c1 : torusParabolicSize (w - z) ^ (-(1 + y₁)) ≤
          2 ^ (1 + y₁) * (3 ^ δ * singularPow (1 + (y₁ + δ)) z w) := by
        have f := rpow_neg_flip_singularPow (p := 1 + y₁) (by linarith) h1
        have l := singularPow_loss_le (p := 1 + y₁) hδ h1
          (torusParabolicSize_le_three_of_abs_le_four (abs_sub_fst_le_four hz1t hw))
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
      -- the combination `|δK(z', v)| s(v - z')^(-(1+y₄))`
      have hR : |K (z' - v) - K (-v)| * torusParabolicSize (v - z') ^ (-(1 + y₄)) ≤
          B * (2 ^ (1 + y₄) * (3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v)) := by
        have h5 : (singularPow 3 z' v + singularPow 3 0 v) * singularPow (1 + y₄) z' v ≤
            3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v := by
          have := add_le_add e1 e2
          linarith [this]
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
      -- left part: `|δK(z, w)| s(w-z)^(..) s(w-z')^(..)`
      have hL : |K (z - w) - K (-w)| * (torusParabolicSize (w - z) ^ (-(1 + y₁)) *
            torusParabolicSize (w - z') ^ (-(1 + y₂))) ≤
          (B * (singularPow 3 z w + singularPow 3 0 w)) *
            ((2 ^ (1 + y₁) * (3 ^ δ * singularPow (1 + (y₁ + δ)) z w)) *
              (2 ^ (1 + y₂) * singularPow (1 + y₂) z' w)) :=
        mul_le_mul a1 (mul_le_mul c1 c2 nW2 (mul_nonneg n21 (mul_nonneg n3 nS1))) (mul_nonneg nW1
          nW2) nA
      have key : (|K (z - w) - K (-w)| * (torusParabolicSize (w - z) ^ (-(1 + y₁)) *
            torusParabolicSize (w - z') ^ (-(1 + y₂)))) *
          ((|K (z' - v) - K (-v)| * torusParabolicSize (v - z') ^ (-(1 + y₄))) *
            (torusParabolicSize (w - v) ^ (-(1 + y₃)) * torusParabolicSize (z - v) ^ (-(1 + y₅)))) ≤
          ((B * (singularPow 3 z w + singularPow 3 0 w)) *
            ((2 ^ (1 + y₁) * (3 ^ δ * singularPow (1 + (y₁ + δ)) z w)) *
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
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_two_lt hKs hz1' (not_le.1 hv)
      unfold i3Psi2dK
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    unfold i3Psi2dK
    rw [this, abs_zero]
    simpa using hrhs'

end RegularityStructures

end
