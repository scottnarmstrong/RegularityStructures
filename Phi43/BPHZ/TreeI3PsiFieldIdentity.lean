/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiFieldCovariance

/-!
# The covariance of `I₃Ψ`: single-scale and two-scale identities

With `F_ε(x, y) = hairerI3PsiField N ρ ε ξ x · y` and `Q = hairerCovariance N ρ ε`:

* two scales: `E[F_ε(x, y) F_ε'(x', ȳ)] = ∫∫ (K(y-w) - K(x-w)) (K(ȳ-w̄) - K(x'-w̄))
  · i3PsiBlockKernel Q_ε Q_{εε'} Q_ε' Q_{εε'} Q_{εε'} Q_{εε'} w y w̄ ȳ dw dw̄`;
* one scale, with the kernel written out and `Q` even:
  `E[F(y) F(ȳ)] = ∫∫ (K(y-w) - K(x-w)) (K(ȳ-w̄) - K(x-w̄))
  [18 Q(w-y) Q(w-w̄)² Q(w̄-ȳ) + 6 Q(w-w̄)³ Q(y-ȳ) + 18 Q(w-w̄)² Q(w-ȳ) Q(w̄-y)] dw dw̄`.

Applying these to `(ε, ε)`, `(ε, ε')`, `(ε', ε')` gives `E|F_ε - F_ε'|²` term by term.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Two-scale covariance of `I₃Ψ`.** -/
theorem hairerI3PsiField_integral_mul_two_scale (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (x x' y y' : SpaceTime) :
    ∫ ω, hairerI3PsiField N ρ ε ξ x ω y * hairerI3PsiField N ρ ε' ξ' x' ω y' ∂P =
      ∫ w, ∫ w', (hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)) *
        (hairerKernelTorus N (y' - w') - hairerKernelTorus N (x' - w')) *
        i3PsiBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovariance N ρ ε ε')
          (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
          (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') w y w' y' :=
  hairerPsiWickCube_testedPair_integral N hρ hε hε' hW hξ hξ'
    ((integrable_hairerKernelTorus_sub N y).sub (integrable_hairerKernelTorus_sub N x))
    ((integrable_hairerKernelTorus_sub N y').sub (integrable_hairerKernelTorus_sub N x')) y y'

/-- **Covariance of `I₃Ψ`.** -/
theorem hairerI3PsiField_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : SpaceTime) :
    ∫ ω, hairerI3PsiField N ρ ε ξ x ω y * hairerI3PsiField N ρ ε ξ x ω y' ∂P =
      ∫ w, ∫ w', (hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)) *
        (hairerKernelTorus N (y' - w') - hairerKernelTorus N (x - w')) *
        (18 * hairerCovariance N ρ ε (w - y) * hairerCovariance N ρ ε (w - w') ^ 2 *
            hairerCovariance N ρ ε (w' - y') +
          6 * hairerCovariance N ρ ε (w - w') ^ 3 * hairerCovariance N ρ ε (y - y') +
          18 * hairerCovariance N ρ ε (w - w') ^ 2 * hairerCovariance N ρ ε (w - y') *
            hairerCovariance N ρ ε (w' - y)) := by
  rw [hairerI3PsiField_integral_mul_two_scale N hρ hε hε hW hξ hξ x x y y']
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  simp only [i3PsiBlockKernel, hairerCrossCovariance_self, hairerCovariance_sub_comm N ρ ε y w']

end RegularityStructures.Phi43

end
