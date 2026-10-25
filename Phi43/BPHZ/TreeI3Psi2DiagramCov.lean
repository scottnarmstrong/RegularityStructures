/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramChaos3Bound
public import Phi43.BPHZ.TreeI3Psi2ChaosOneBound

/-!
# Deterministic bound for the covariance of the field of `I(Ψ³)Ψ²`

`i3Psi2Cov_bound_uniform`: for `0 < s(z), s(z') ≤ 1` and `s(z - z') > 0`,
`|i3Psi2Cov K Q c z z'| ≤ C · i3Psi2Target δ z z'`, where `i3Psi2Target δ z z' = s(z - z')^(-(1+δ))
+ s(z - z')^(-2) (s z^(1-δ) + s z'^(1-δ)) + s(z - z')^(-1) (s z^(-δ) + s z'^(-δ)) + s z^(-(1+2δ)) +
s z'^(-(1+2δ))` (the pairs `(0, -1-δ)`, `(1-δ, -2)`, `(-δ, -1)`, `(-1-2δ,
0)` of [Hai14, p. 170--171]) and `C` depends only on `B, δ`. Here `i3Psi2Cov` is the abstract form
of `hairerI3Psi2Cov` (all six terms). This is the deterministic half of the second-moment bound for
`I(Ψ³)Ψ²` in [Hai14, p. 170--171].
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Deterministic bound for the covariance of `I(Ψ³)Ψ²`** ([Hai14, p. 170--171]). -/
theorem i3Psi2Cov_bound_uniform {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ} {M c : ℝ}, Measurable K →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |J (u + h) - J u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x, |J x| ≤ M) → Integrable J → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, Q x = ∫ w, J (x + w) * J w) → c = 2 * ∫ x, K x * Q x ^ 2 →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        0 < torusParabolicSize (z - z') → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
          |i3Psi2Cov K Q c z z'| ≤ C * i3Psi2Target δ z z' := by
  obtain ⟨C5, hC5, h5⟩ := i3Psi2Double5_bound_uniform hB hδ hδ1
  obtain ⟨C3, hC3, h3⟩ := i3Psi2Double3_bound_uniform hB hδ hδ1
  obtain ⟨C1, hC1, h1⟩ := i3Psi2Chaos1Total_bound_uniform hB hδ hδ1
  refine ⟨C5 + C3 + C1, by positivity, ?_⟩
  intro K J Q M c hKm hKs hK hKinc hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hz hz' hzz hz1 hz1'
  have hQe := i3Psi2_Q_neg hQJ
  obtain ⟨_, b5⟩ := h5 hKm hKs hK hKinc hQm hQ hQe z z' hz hz' hzz hz1 hz1'
  obtain ⟨_, b3⟩ := h3 hKm hKs hK hQm hQ hQe z z' hz hz' hzz hz1 hz1'
  have b1 := h1 hKm hKs hK hJm hJ hJinc hJb hJi hQm hQ hQJ hc z z' hz hz' hzz hz1 hz1'
  rw [i3Psi2Cov_eq]
  have x1 := abs_add_le (i3Psi2Double K (i3Psi2Chaos5 Q) z z' +
    i3Psi2Double K (i3Psi2Chaos3 Q) z z') (i3Psi2Chaos1Total K Q c z z')
  have x2 := abs_add_le (i3Psi2Double K (i3Psi2Chaos5 Q) z z')
    (i3Psi2Double K (i3Psi2Chaos3 Q) z z')
  have T0 := i3Psi2Target_nonneg δ z z'
  nlinarith

end RegularityStructures

end
