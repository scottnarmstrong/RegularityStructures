/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGrad
public import Phi43.BPHZ.GammaMomentLp
import Mathlib.Tactic

/-!
# All moments of `g_i` and `v₁`

`g_i` and `v₁` are kernel-tested linear functionals of the Gaussian field `Ψ`.  By
`integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation` (degree `1`) all moments are
controlled by the second moment, and `gammaMoment_lintegral_enorm_pow_le` gives the Kolmogorov
(`lintegral`) form, for every `q ≥ 1`, uniformly in `ε ∈ (0, 1]`, the base point and the probability
space:

* `gammaGrad_lintegral_enorm_pow_le`: `∫⁻ ‖g_i‖ₑ^q ≤ ofReal (C d^((1-δ)/2))^q`, `d = s(y - x) ≤ 1`;
  `gammaGrad_lintegral_enorm_pow_le_kappa`: exponent `1/2 - κ + κ̄`;
* `gammaPsiTaylor_lintegral_enorm_pow_le`: `∫⁻ ‖v₁‖ₑ^q ≤ ofReal (C r^((3-δ)/2))^q`, `r = ‖(t, a)‖ ≤ 1/2`;
  `gammaPsiTaylor_lintegral_enorm_pow_le_kappa`: exponent `3/2 - κ + κ̄`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- All moments of a kernel-tested copy of `Ψ`. -/
theorem gammaPsi_tested_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g →
        Integrable (fun ω => (∫ w, g w * hairerPsiField N ξ ω w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, g w * hairerPsiField N ξ ω w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, g w * hairerPsiField N ξ ω w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {g} hgm hgi => ?_⟩
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Polynomial.X (by simp)
  have e : ∀ ω, (∫ w, g w * hairerPsiField N ξ ω w) =
      ∫ w, Polynomial.X.eval (hairerPsiField N ξ ω w) * g w := fun ω => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [mul_comm]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
