/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestWickCov
public import Phi43.BPHZ.CrossMollifierPsi

/-!
# Second moment of the cross-mollifier difference of `Ψ` against the periodised semigroup kernel

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise, `θ ∈ (0, 1]`, `t ∈ (0, 1]`, `lam = t^(1/4)` and every `x`,
`E|∫ (Ψ_{ρ,ε} - Ψ_{ρ',ε'}) q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(-(1+2θ))`
(`hairerPsiField_sub_semigroupPeriodised_second_moment_le`), with `C` independent of `ε`, `ε'`, `t`,
`x`.  The covariance of the difference is `hairerKernelDiffCovarianceTwo (u - v)` and satisfies
`|Δ(z)| ≲ (max ε ε')^(2θ) s(z)^(-1-2θ)` globally (`hairerKernelDiffCovarianceTwo_abs_le`), so
`exists_semigroupPeriodised_second_moment_le_cov` applies with `e = -(1 + 2θ)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the tested cross-mollifier difference of `Ψ`, semigroup test.** -/
theorem hairerPsiField_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * θ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨Cd, hCd0, hCd⟩ := exists_semigroupPeriodised_second_moment_le_cov.{u}
    (e := -(1 + 2 * θ)) (by linarith)
  refine ⟨Cd * A, mul_nonneg hCd0 hA, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  have hM0 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiField_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have h := hCd (P := P)
    ((measurable_hairerPsiField_uncurry N hξ).sub (measurable_hairerPsiField_uncurry N hξ'))
    (fun u => (hairerPsiField_memLp N hρ hε.1 hW hξ u).sub
      (hairerPsiField_memLp N hρ' hε'.1 hW hξ' u))
    (M := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' 0) (fun u => by
      have := hcov u u
      rw [sub_self] at this
      exact this.le)
    (Φ := fun u v => hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (u - v)) hcov
    (A := A * (max ε ε') ^ (2 * θ)) (mul_nonneg hA hM0) (fun u v hs => by
      have := hQ hε.1 hε.2 hε'.1 hε'.2 (u - v) hs
      rwa [show -1 - 2 * θ = -(1 + 2 * θ) by ring] at this) ht ht1 x
  refine h.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end
