/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLevel
public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise

/-!
# The weighted diagram `N₁` of `I(Ψ³)Ψ²` with general exponents

The diagram `N₁` (chaos `5`) is the double integral of
`δK(z, w) δK(z', v) · s(w - z')^(-2) s(w - v)^(-1) s(z - v)^(-2)` against a covariance-independent
weight.  In the difference of the fields at two scales (or two mollifiers) one of the five
covariance factors gains a factor `μ s^(-θ)`, so the exponents become `2 + x₁`, `1 + x₂`, `2 + x₃`
with small `xᵢ ≥ 0`.  We prove, for every measurable `F` dominated by this weight, that
`F` is integrable on the product and `|∫∫ F| ≤ C S_{1 + δ + x₁ + x₂ + x₃}(z, z')`, where
`S_p(z, z') = s(z - z')^(-p) + s(z)^(-p) + s(z')^(-p)` (`i3Psi2S`).
The loss `δ > 0` of the exponent of the first factor on the time slab is the one of
[Hai14, p. 170--171].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The majorant of the diagram `N₁`: exponents `2 + ν` at `(z', w)`, `a₃` at `(z, v)`, `a₂` at
`(w, v)`. -/
def i3Psi2N1Majorant (ν a₂ a₃ : ℝ) (z z' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (2 + ν) z' w) *
    ((singularPow 3 z' v + singularPow 3 0 v) * singularPow a₃ z v * singularPow a₂ w v)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2N1Majorant_nonneg (ν a₂ a₃ : ℝ) (z z' w v : SpaceTime) :
    0 ≤ i3Psi2N1Majorant ν a₂ a₃ z z' w v := by
  unfold i3Psi2N1Majorant
  have := singularPow_nonneg
  exact mul_nonneg (mul_nonneg (add_nonneg (this _ _ _) (this _ _ _)) (this _ _ _))
    (mul_nonneg (mul_nonneg (add_nonneg (this _ _ _) (this _ _ _)) (this _ _ _)) (this _ _ _))

/-- A centred power loses `δ` of its exponent on a ball of radius `3`. -/
theorem singularPow_loss_le {p δ : ℝ} (hδ : 0 ≤ δ) {c w : SpaceTime}
    (h : 0 < torusParabolicSize (c - w)) (h3 : torusParabolicSize (c - w) ≤ 3) :
    singularPow p c w ≤ 3 ^ δ * singularPow (p + δ) c w := by
  have hpow : singularPow p c w = torusParabolicSize (c - w) ^ δ * singularPow (p + δ) c w := by
    unfold singularPow
    rw [← Real.rpow_add h]; congr 1; ring
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h.le h3 hδ) (singularPow_nonneg _ _ _)

/-- **Pointwise domination of the weight of `N₁`.** -/
theorem abs_dK_dK_N1_le {K : SpaceTime → ℝ} {B δ x₁ x₂ x₃ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : 0 ≤ x₁)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v)) :
    |i3Psi2dK K z w| * |i3Psi2dK K z' v| *
        (torusParabolicSize (w - z') ^ (-(2 + x₁)) * torusParabolicSize (w - v) ^ (-(1 + x₂)) *
          torusParabolicSize (z - v) ^ (-(2 + x₃))) ≤
      (B ^ 2 * (2 ^ (2 + x₁) * 3 ^ δ)) *
        i3Psi2N1Majorant (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have n2 : (0 : ℝ) ≤ 2 ^ (2 + x₁) := Real.rpow_nonneg (by norm_num) _
  have hrhs := i3Psi2N1Majorant_nonneg (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v
  have hrhs' : 0 ≤ (B ^ 2 * (2 ^ (2 + x₁) * 3 ^ δ)) *
      i3Psi2N1Majorant (x₁ + δ) (1 + x₂) (2 + x₃) z z' w v :=
    mul_nonneg (mul_nonneg (sq_nonneg B) (mul_nonneg n2 n3)) hrhs
  by_cases hw : |w.1| ≤ 2
  · by_cases hv : |v.1| ≤ 2
    · have hz1t := abs_fst_le_one_of_size_le_one hz1'
      have a1 := abs_dK_le hK h1 h0
      have a2 := abs_dK_le hK h1' h0'
      have c1 : torusParabolicSize (w - z') ^ (-(2 + x₁)) ≤
          2 ^ (2 + x₁) * (3 ^ δ * singularPow (2 + (x₁ + δ)) z' w) := by
        have f := rpow_neg_flip_singularPow (p := 2 + x₁) (by linarith) hz'w
        have l := singularPow_loss_le (p := 2 + x₁) hδ hz'w
          (torusParabolicSize_le_three_of_abs_le_four (abs_sub_fst_le_four hz1t hw))
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
          ((2 ^ (2 + x₁) * (3 ^ δ * singularPow (2 + (x₁ + δ)) z' w)) *
            torusParabolicSize (w - v) ^ (-(1 + x₂)) * torusParabolicSize (z - v) ^ (-(2 + x₃))) :=
        mul_le_mul (mul_le_mul a1 a2 (abs_nonneg _) nA)
          (mul_le_mul (mul_le_mul c1 le_rfl nW2 (mul_nonneg n2 (mul_nonneg n3
            (singularPow_nonneg _ _ _)))) le_rfl nW3
            (mul_nonneg (mul_nonneg n2 (mul_nonneg n3 (singularPow_nonneg _ _ _))) nW2))
          (mul_nonneg (mul_nonneg nW1 nW2) nW3) (mul_nonneg nA nB)
      refine key.trans (le_of_eq ?_)
      unfold i3Psi2N1Majorant singularPow
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

