/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Phi43.BPHZ.TreeI3PsiPrincipal

/-!
# The diagram `N₁` of the chaos-`5` kernel of `I(Ψ³)Ψ²`

The last term `36 Q(w - z̄) ² Q(z - w̄)² Q(w - w̄)` of the chaos-`5` kernel `χ₅`, integrated against
`δK(z, w) δK(z̄, w̄)`:
`i3Psi2N1 K Q z z' w v = δK(z, w) Q(w - z')² Q(w - v) δK(z', v) Q(z - v)²`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The integrand of the diagram `N₁` (without the combinatorial factor `36`). -/
def i3Psi2N1 (K Q : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  i3Psi2dK K z w * Q (w - z') ^ 2 * (Q (w - v) * (i3Psi2dK K z' v * Q (z - v) ^ 2))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- Pointwise majorant of the diagram `N₁`. -/
theorem abs_i3Psi2N1_le {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQe : ∀ x, Q (-x) = Q x) {z z' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hzv : 0 < torusParabolicSize (z - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |i3Psi2N1 K Q z z' w v| ≤
      (B ^ 7 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) * singularPow (2 + δ) z' w) *
        ((singularPow 3 z' v + singularPow 3 0 v) * singularPow 2 z v * singularPow 1 w v)) := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (B ^ 7 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) *
      singularPow (2 + δ) z' w) * ((singularPow 3 z' v + singularPow 3 0 v) *
        singularPow 2 z v * singularPow 1 w v)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hB 7) n3) (mul_nonneg (mul_nonneg
      (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      (singularPow_nonneg _ _ _)) (mul_nonneg (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
      (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _)))
  by_cases hw : |w.1| ≤ 2
  · by_cases hv : |v.1| ≤ 2
    · have hz1t := abs_fst_le_one_of_size_le_one hz1'
      have a1 := abs_dK_le hK h1 h0
      have a2 := abs_dK_le hK h1' h0'
      have q1 : |Q (w - z')| ^ 2 ≤ B ^ 2 * 3 ^ δ * singularPow (2 + δ) z' w := by
        rw [Q_sub_comm hQe w z']
        exact abs_Q_sq_le_singularPow_loss hδ hQ hz'w (abs_sub_fst_le_four hz1t hw)
      have q2 := abs_Q_le_singularPow hQ (c := w) (w := v) hwv
      have q3 := abs_Q_sq_le_singularPow hQ hzv
      have e : |i3Psi2N1 K Q z z' w v| = |i3Psi2dK K z w| * |Q (w - z')| ^ 2 *
          (|Q (w - v)| * (|i3Psi2dK K z' v| * |Q (z - v)| ^ 2)) := by
        unfold i3Psi2N1
        simp only [abs_mul, abs_pow]
      rw [e]
      unfold i3Psi2dK at a1 a2 ⊢
      have nA : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have nB : 0 ≤ B * (singularPow 3 z' v + singularPow 3 0 v) :=
        mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      have nQ : 0 ≤ B * singularPow 1 w v := mul_nonneg hB (singularPow_nonneg _ _ _)
      have key : |K (z - w) - K (-w)| * |Q (w - z')| ^ 2 *
          (|Q (w - v)| * (|K (z' - v) - K (-v)| * |Q (z - v)| ^ 2)) ≤
          (B * (singularPow 3 z w + singularPow 3 0 w)) *
            (B ^ 2 * 3 ^ δ * singularPow (2 + δ) z' w) *
          ((B * singularPow 1 w v) * ((B * (singularPow 3 z' v + singularPow 3 0 v)) *
            (B ^ 2 * singularPow 2 z v))) := by
        refine mul_le_mul (mul_le_mul a1 q1 (sq_nonneg _) nA)
          (mul_le_mul q2 (mul_le_mul a2 q3 (sq_nonneg _) nB) (mul_nonneg (abs_nonneg _)
            (sq_nonneg _)) nQ) (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (sq_nonneg _)))
          (mul_nonneg nA (mul_nonneg (mul_nonneg (sq_nonneg B) n3) (singularPow_nonneg _ _ _)))
      refine key.trans (le_of_eq ?_)
      ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_two_lt hKs hz1' (not_le.1 hv)
      have h0 : i3Psi2N1 K Q z z' w v = 0 := by
        unfold i3Psi2N1 i3Psi2dK
        rw [this]
        ring
      rw [h0, abs_zero]
      exact hrhs
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    have h0 : i3Psi2N1 K Q z z' w v = 0 := by
      unfold i3Psi2N1 i3Psi2dK
      rw [this]
      ring
    rw [h0, abs_zero]
    exact hrhs

end RegularityStructures

end
