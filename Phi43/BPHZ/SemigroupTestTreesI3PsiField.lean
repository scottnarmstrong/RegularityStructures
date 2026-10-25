/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3PsiCov
public import Phi43.BPHZ.TreeI3Psi2ChaosOneBasic

/-!
# The global covariance bound for the field `I₃Ψ_x`

`hairerI3PsiField_cov_bound_global`: for all `x, y, y'` with `y, y' ≠ x` and `y ≠ y'`, uniformly in
`ε ∈ (0, 1]`,
`|E[I₃Ψ_x(y) I₃Ψ_x(y')]| ≤ C (1 + s(y - x)² + s(y' - x)²)
  (s(y - y')^(-1) + s(y - y')^(-δ) + s(y - x)^(-δ) + s(y' - x)^(-δ))`.
There is no restriction `s(y - x), s(y' - x) ≤ 1`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Global covariance bound for `I₃Ψ_x`**, uniform in `ε ∈ (0, 1]` and the base point. -/
theorem hairerI3PsiField_cov_bound_global (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, hairerI3PsiField N ρ ε ξ x ω y * hairerI3PsiField N ρ ε ξ x ω y' ∂P| ≤
            C * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) *
              (torusParabolicSize (y - y') ^ (-(1 : ℝ)) + torusParabolicSize (y - y') ^ (-δ) +
                torusParabolicSize (y - x) ^ (-δ) + torusParabolicSize (y' - x) ^ (-δ)) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  have hB : 0 ≤ CK + CQ := by linarith
  obtain ⟨C, hC, hdiag⟩ := i3PsiPairing_bound_global (B := CK + CQ) hB hδ hδ1
  refine ⟨4 * C, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hz hz' hzz
  rw [hairerI3PsiField_integral_mul_eq_pairing N hρ hε.1 hW hξ x y y']
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ (CK + CQ) * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hQ' : ∀ z, 0 < torusParabolicSize z →
      |hairerCovariance N ρ ε z| ≤ (CK + CQ) * torusParabolicSize z ^ (-(1 : ℝ)) :=
    fun z hz => (hQ hε.1 hε.2 z hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  set T : ℝ := |(y - x).1| + |(y' - x).1| + 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hD : ∀ w v : SpaceTime, |w.1| ≤ |(y - x).1| + 1 → |v.1| ≤ |(y' - x).1| + 1 →
      torusParabolicSize (w - v) ≤ √T + 1 := by
    intro w v hw hv
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (w - v).1 = w.1 - v.1 := rfl
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [hT]
    linarith
  have := hdiag (measurable_constantsComparison_hairerKernelTorus N) hK'
    (fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz)
    (constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2) hQ' (y - x) (y' - x)
    (by positivity) hD hzz' hz hz'
  rw [sub_sub_sub_cancel_right] at this
  refine this.trans ?_
  -- compare the polynomial prefactors
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e2 := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hsq : √T ≤ (1 + T) / 2 := by
    nlinarith [Real.sq_sqrt hT0, sq_nonneg (√T - 1)]
  have hpre : 1 + (√T + 1) + |(y - x).1| ≤
      4 * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) := by
    have := sq_nonneg (torusParabolicSize (y - x))
    have := sq_nonneg (torusParabolicSize (y' - x))
    rw [hT] at hsq
    linarith
  have hS : 0 ≤ torusParabolicSize (y - y') ^ (-(1 : ℝ)) + torusParabolicSize (y - y') ^ (-δ) +
      torusParabolicSize (y - x) ^ (-δ) + torusParabolicSize (y' - x) ^ (-δ) := by
    have a1 : 0 ≤ torusParabolicSize (y - y') ^ (-(1 : ℝ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a2 : 0 ≤ torusParabolicSize (y - y') ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a3 : 0 ≤ torusParabolicSize (y - x) ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have a4 : 0 ≤ torusParabolicSize (y' - x) ^ (-δ) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    linarith
  calc C * (1 + (√T + 1) + |(y - x).1|) * (torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
        torusParabolicSize (y - y') ^ (-δ) + torusParabolicSize (y - x) ^ (-δ) +
        torusParabolicSize (y' - x) ^ (-δ))
      ≤ C * (4 * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2)) *
        (torusParabolicSize (y - y') ^ (-(1 : ℝ)) + torusParabolicSize (y - y') ^ (-δ) +
        torusParabolicSize (y - x) ^ (-δ) + torusParabolicSize (y' - x) ^ (-δ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpre hC) hS
    _ = _ := by ring

end RegularityStructures.Phi43

end
