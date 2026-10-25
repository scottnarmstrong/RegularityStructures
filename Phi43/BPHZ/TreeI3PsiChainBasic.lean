/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiOuter
public import Phi43.BPHZ.TreeI3PsiPointwise

/-!
# Building blocks for the chain diagrams

The chain integrand `δK(z, w) Q(w - u) · Q(w - v)² · δK(z', v) Q(v - u')`, its pointwise
majorants by centred powers, the inner integral over `v`, and the symmetrisation of the
exponents `s(a - b)^(-δ)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The chain integrand
`δK(z, w) Q(w - u) · Q(w - v)² · δK(z', v) Q(v - u')` of the diagrams with two `Q²`-links. -/
def i3PsiChain (K Q : SpaceTime → ℝ) (z z' u u' w v : SpaceTime) : ℝ :=
  (K (z - w) - K (-w)) * Q (w - u) *
    (Q (w - v) ^ 2 * ((K (z' - v) - K (-v)) * Q (v - u')))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem singularPow_three_mul_one_le {p q w : SpaceTime}
    (hp : 0 < torusParabolicSize (p - w)) (hq : 0 < torusParabolicSize (q - w)) :
    singularPow 3 p w * singularPow 1 q w ≤ singularPow 4 p w + singularPow 4 q w := by
  have := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) hp hq
  norm_num at this
  exact this

/-- Left majorant of the chain integrand. -/
theorem abs_dK_mul_Q_le {K Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {z u w : SpaceTime} (h1 : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) (hu : 0 < torusParabolicSize (u - w)) :
    |(K (z - w) - K (-w)) * Q (w - u)| ≤
      2 * B ^ 2 * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w) := by
  rw [abs_mul]
  have a1 := abs_dK_le hK h1 h0
  have a2 := abs_Q_flip_le hB hQ hu
  have n1 : 0 ≤ singularPow 3 z w + singularPow 3 0 w :=
    add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
  calc |K (z - w) - K (-w)| * |Q (w - u)|
      ≤ (B * (singularPow 3 z w + singularPow 3 0 w)) * (2 * B * singularPow 1 u w) :=
        mul_le_mul a1 a2 (abs_nonneg _) (mul_nonneg hB n1)
    _ = _ := by ring

/-- Right majorant of the chain integrand, by pure powers of order `4`. -/
theorem abs_dK_mul_Q_le_pow_four {K Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {z u w : SpaceTime} (h1 : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) (hu : 0 < torusParabolicSize (u - w)) :
    |(K (z - w) - K (-w)) * Q (w - u)| ≤
      2 * B ^ 2 * (singularPow 4 z w + singularPow 4 0 w + 2 * singularPow 4 u w) := by
  refine (abs_dK_mul_Q_le hB hK hQ h1 h0 hu).trans ?_
  have e1 := singularPow_three_mul_one_le h1 hu
  have e2 := singularPow_three_mul_one_le h0 hu
  have : (singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w ≤
      singularPow 4 z w + singularPow 4 0 w + 2 * singularPow 4 u w := by
    rw [add_mul]; linarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

end RegularityStructures

end
