/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Phi43.BPHZ.TreeI3PsiPrincipal

/-!
# The diagram `N₂` of the chaos-`3` kernel of `I(Ψ³)Ψ²`

The second term `144 Q(w - z) Q(w - w̄) Q(w - z̄) Q(z - w̄) Q(w̄ - z̄)` of the chaos-`3` kernel `χ₃`,
integrated against `δK(z, w) δK(z̄, w̄)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The integrand of the diagram `N₂` (without the combinatorial factor `144`). -/
def i3Psi2N2 (K Q : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  i3Psi2dK K z w * (Q (w - z) * Q (w - z')) *
    (Q (w - v) * (i3Psi2dK K z' v * Q (v - z')) * Q (z - v))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- Pointwise majorant of the diagram `N₂`. -/
theorem abs_i3Psi2N2_le {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQe : ∀ x, Q (-x) = Q x) {z z' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hz'w : 0 < torusParabolicSize (z' - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hzv : 0 < torusParabolicSize (z - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |i3Psi2N2 K Q z z' w v| ≤
      (2 * B ^ 7 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + δ) z w *
        singularPow 1 z' w) * ((3 * singularPow 4 z' v + singularPow 4 0 v) *
          singularPow 1 z v * singularPow 1 w v)) := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (2 * B ^ 7 * 3 ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) *
      singularPow (1 + δ) z w * singularPow 1 z' w) * ((3 * singularPow 4 z' v +
        singularPow 4 0 v) * singularPow 1 z v * singularPow 1 w v)) := by
    have := singularPow_nonneg 3 z w
    have := singularPow_nonneg 3 0 w
    have := singularPow_nonneg 4 z' v
    have := singularPow_nonneg 4 0 v
    have := singularPow_nonneg (1 + δ) z w
    have := singularPow_nonneg 1 z' w
    have := singularPow_nonneg 1 z v
    have := singularPow_nonneg 1 w v
    positivity
  by_cases hw : |w.1| ≤ 2
  · have hz1t := abs_fst_le_one_of_size_le_one hz1
    have a1 := abs_dK_le hK h1 h0
    have a2 : |Q (w - z)| ≤ B * 3 ^ δ * singularPow (1 + δ) z w := by
      rw [Q_sub_comm hQe w z]
      exact abs_Q_le_lower hB hδ hQ h1 (abs_sub_fst_le_four hz1t hw)
    have a3 : |Q (w - z')| ≤ B * singularPow 1 z' w := by
      rw [Q_sub_comm hQe w z']
      exact abs_Q_le_singularPow hQ hz'w
    have a4 := abs_Q_le_singularPow hQ (c := w) (w := v) hwv
    have a5 := abs_dK_mul_Q_le_pow_four hB hK hQ h1' h0' (u := z') (w := v) h1'
    have a6 := abs_Q_le_singularPow hQ hzv
    have e : |i3Psi2N2 K Q z z' w v| = |i3Psi2dK K z w| * (|Q (w - z)| * |Q (w - z')|) *
        (|Q (w - v)| * |i3Psi2dK K z' v * Q (v - z')| * |Q (z - v)|) := by
      unfold i3Psi2N2
      simp only [abs_mul]
    rw [e]
    unfold i3Psi2dK at a1 ⊢
    have nA : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
      mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
    have nB : 0 ≤ B * 3 ^ δ * singularPow (1 + δ) z w :=
      mul_nonneg (mul_nonneg hB n3) (singularPow_nonneg _ _ _)
    have nC : 0 ≤ B * singularPow 1 z' w := mul_nonneg hB (singularPow_nonneg _ _ _)
    have nD : 0 ≤ B * singularPow 1 w v := mul_nonneg hB (singularPow_nonneg _ _ _)
    have nE : 0 ≤ 2 * B ^ 2 * (singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 z' v) := by
      have := singularPow_nonneg 4 z' v
      have := singularPow_nonneg 4 0 v
      positivity
    have nF : 0 ≤ B * singularPow 1 z v := mul_nonneg hB (singularPow_nonneg _ _ _)
    have key : |K (z - w) - K (-w)| * (|Q (w - z)| * |Q (w - z')|) *
        (|Q (w - v)| * |(K (z' - v) - K (-v)) * Q (v - z')| * |Q (z - v)|) ≤
        (B * (singularPow 3 z w + singularPow 3 0 w)) *
          ((B * 3 ^ δ * singularPow (1 + δ) z w) * (B * singularPow 1 z' w)) *
        ((B * singularPow 1 w v) * (2 * B ^ 2 * (singularPow 4 z' v + singularPow 4 0 v +
          2 * singularPow 4 z' v)) * (B * singularPow 1 z v)) := by
      refine mul_le_mul (mul_le_mul a1 (mul_le_mul a2 a3 (abs_nonneg _) nB) (mul_nonneg
        (abs_nonneg _) (abs_nonneg _)) nA) (mul_le_mul (mul_le_mul a4 a5 (abs_nonneg _) nD) a6
        (abs_nonneg _) (mul_nonneg nD nE)) (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (abs_nonneg _)) (mul_nonneg nA (mul_nonneg nB nC))
    refine key.trans (le_of_eq ?_)
    ring
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    have h0 : i3Psi2N2 K Q z z' w v = 0 := by
      unfold i3Psi2N2 i3Psi2dK
      rw [this]
      ring
    rw [h0, abs_zero]
    exact hrhs

end RegularityStructures

end
