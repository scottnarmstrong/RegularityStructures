/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentWick
public import Phi43.BPHZ.GammaMomentMajorant
import Mathlib.Tactic

/-!
# Second moment of a kernel-tested copy of `Ψ` with a majorant kernel

For a measurable integrable kernel `A` with the majorant `gammaMajorant A x y r M a p` and
`4 < p < 9/2`, uniformly in `ε ∈ (0, 1]`,
`E |∫ A Ψ|² ≤ C M² r^a r^a`.  The covariance of `Ψ` is bounded by `s⁻¹`
(`hairerCovariance_abs_le`) and the principal pairing is `gammaMajorant_lint_diag` with `e = 1`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of a majorant-kernel pairing of `Ψ`.** -/
theorem gammaPsi_tested_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {a p : ℝ} (hp4 : 4 < p) (hp5 : p < 5) (hpp : 2 * p < 9) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ}, gammaMajorant A x y r M a p →
        Integrable A → |y.1 - x.1| ≤ 1 →
        ∫ ω, (∫ w, A w * hairerPsiField N ξ ω w) ^ 2 ∂P ≤ C * M * M * r ^ a * r ^ a := by
  obtain ⟨CD, hCD, hD⟩ := gammaMajorant_lint_diag (a := a) (a' := a) (p := p) (p' := p) (e := 1)
    (by linarith) hp5 (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨2 * BQ * CD, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ A x y r M hA hAi hxy
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiField_integral_mul N hρ hε.1 hW hξ
  have hlint := hD hA hA hxy hxy
  have hM := hA.2.1
  have hr := hA.1
  have key := gammaMoment_second_le_of_lintBound (P := P) (Y := hairerPsiField N ξ)
    (measurable_hairerPsiField_uncurry N hξ)
    (fun u => hairerPsiField_memLp N hρ hε.1 hW hξ u) (M₀ := hairerCovariance N ρ ε 0)
    (fun u => by rw [hcov u u, sub_self])
    (R := hairerCovariance N ρ ε) hcov (p := 1) (A := 2 * BQ) (by positivity)
    (fun u v h => by
      have := abs_cov_flip_le hBQ (hQ hε.1 hε.2) h
      exact this)
    hA.2.2.1 hAi (M := CD * M * M * r ^ a * r ^ a)
    (by
      have := Real.rpow_nonneg hr a
      positivity) (by simpa using hlint)
  have e : ∀ ω, |∫ w, hairerPsiField N ξ ω w * A w| ^ 2 =
      (∫ w, A w * hairerPsiField N ξ ω w) ^ 2 := fun ω => by
    simp only [sq_abs, mul_comm]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end
