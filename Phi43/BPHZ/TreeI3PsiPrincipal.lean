/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChainBasic
public import Phi43.BPHZ.TreeI3PsiTwoLevel

/-!
# The principal pairing of the tree `I(Ψ³)Ψ`

The double integral `∫∫ δK(z, w) δK(z', w̄) Q(w - w̄)³ dw dw̄` (the factor `δ²Q^{(3)}(z, z')` of
[Hai14, p. 167]) is absolutely integrable and bounded by `C s(z')^θ` for every `θ ∈ (0, 1)`,
provided `s(z) ≤ 1` and `s(z') ≤ 1`.  The Hölder gain `s(z')^θ` comes from the increment bound of
`K` (Lemma 10.18); the remaining convolution has total order `4 + θ < 5`, hence is bounded on the
time slab `|t| ≤ 2` carrying the support of `δK(z, ·)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167, last display.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The integrand `δK(z, w) δK(z', v) Q(w - v)³` of the principal pairing. -/
def i3PsiPrincipal (K Q : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  (K (z - w) - K (-w)) * (K (z' - v) - K (-v)) * Q (w - v) ^ 3

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The recentred kernel vanishes outside the time slab `|t| ≤ 2` when `s(z) ≤ 1`. -/
theorem dK_eq_zero_of_two_lt {K : SpaceTime → ℝ} (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    {z w : SpaceTime} (hz : torusParabolicSize z ≤ 1) (hw : 2 < |w.1|) :
    K (z - w) - K (-w) = 0 := by
  have h1 : √|z.1| ≤ 1 := by
    have := torusSpatialNorm_nonneg z.2
    unfold torusParabolicSize at hz
    linarith
  have hzt : |z.1| ≤ 1 := by
    have := Real.sqrt_le_iff.1 h1
    linarith [this.2]
  have e1 : K (z - w) = 0 := by
    apply hKs
    have : (z - w).1 = z.1 - w.1 := rfl
    rw [this]
    have h := abs_sub_abs_le_abs_sub w.1 z.1
    rw [abs_sub_comm] at h
    linarith
  have e2 : K (-w) = 0 := by
    apply hKs
    have : (-w).1 = -w.1 := rfl
    rw [this, abs_neg]
    linarith
  rw [e1, e2, sub_zero]

end RegularityStructures

end
