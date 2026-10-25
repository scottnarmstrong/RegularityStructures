/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiTestedMoment
public import Phi43.BPHZ.TreeI3PsiDiagramUniform
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.BPHZ.HairerKernelIncrementTorus
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.Stochastic.ConstantsComparisonC2Bounds

/-!
# The pointwise covariance bound for `I₃Ψ`

The covariance `E[I₃Ψ_x(y) I₃Ψ_x(ȳ)]` equals the diagram `i3PsiPairing K Q (y - x) (ȳ - x)` with
`K = hairerKernelTorus N`, `Q = hairerCovariance N ρ ε` (translate the integration variables by `x`),
and `i3PsiPairing_bound_uniform` bounds it, with a constant independent of `ε ∈ (0, 1]` and `x`,
by `C (s(y-ȳ)^(-δ) + s(y-x)^(-δ) + s(ȳ-x)^(-δ) + s(y-ȳ)^(-1) (s(y-x)^(1-δ) + s(ȳ-x)^(1-δ)))`
whenever `s(y - x), s(ȳ - x) ≤ 1` and `y, ȳ, x` are distinct.

**Time support.**  The covariance `Q_ε = K_ε ⋆ K_ε^-` does not vanish for `|z.1| > 2` when the
mollifier has positive time radius (its time support is `2 (1 + ε² R)`); the bound
`i3PsiPairing_bound_uniform` does not need such a time support condition
(see `Phi43.BPHZ.TreeI3PsiDiagramSlab`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- Translating the integration variables by the base point `x`. -/
theorem hairerI3PsiField_integral_mul_eq_pairing (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : SpaceTime) :
    ∫ ω, hairerI3PsiField N ρ ε ξ x ω y * hairerI3PsiField N ρ ε ξ x ω y' ∂P =
      i3PsiPairing (hairerKernelTorus N) (hairerCovariance N ρ ε) (y - x) (y' - x) := by
  rw [hairerI3PsiField_integral_mul N hρ hε hW hξ x y y']
  have key : ∀ H : SpaceTime → SpaceTime → ℝ,
      ∫ w, ∫ w', H w w' = ∫ a, ∫ b, H (x + a) (x + b) := by
    intro H
    rw [← integral_comp_add_left_spaceTime (fun w => ∫ w', H w w') x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact (integral_comp_add_left_spaceTime (fun w' => H (x + a) w') x).symm
  rw [key]
  unfold i3PsiPairing i3PsiDiagramIntegrand
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have e1 : y - (x + a) = y - x - a := by abel
  have e2 : x - (x + a) = -a := by abel
  have e3 : y' - (x + b) = y' - x - b := by abel
  have e4 : x - (x + b) = -b := by abel
  have e5 : x + a - y = a - (y - x) := by abel
  have e6 : x + a - (x + b) = a - b := by abel
  have e7 : x + b - y' = b - (y' - x) := by abel
  have e8 : y - y' = y - x - (y' - x) := by abel
  have e9 : x + a - y' = a - (y' - x) := by abel
  have e10 : x + b - y = b - (y - x) := by abel
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

/-- **Pointwise covariance bound for `I₃Ψ`**, uniform in `ε ∈ (0, 1]` and the base point `x`
([Hai14, (10.36)--(10.38)]): for `δ ∈ (0, 1/4]`, distinct points `y, ȳ, x` with
`s(y - x), s(ȳ - x) ≤ 1`,
`|E[I₃Ψ_x(y) I₃Ψ_x(ȳ)]| ≤ C (s(y-ȳ)^(-δ) + s(y-x)^(-δ) + s(ȳ-x)^(-δ) +
  s(y-ȳ)^(-1) (s(y-x)^(1-δ) + s(ȳ-x)^(1-δ)))`. -/
theorem hairerI3PsiField_cov_bound (N : ℕ) (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') → torusParabolicSize (y - x) ≤ 1 →
        torusParabolicSize (y' - x) ≤ 1 →
          |∫ ω, hairerI3PsiField N ρ ε ξ x ω y * hairerI3PsiField N ρ ε ξ x ω y' ∂P| ≤
            C * (torusParabolicSize (y - y') ^ (-δ) + torusParabolicSize (y - x) ^ (-δ) +
              torusParabolicSize (y' - x) ^ (-δ) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
                (torusParabolicSize (y - x) ^ (1 - δ) + torusParabolicSize (y' - x) ^ (1 - δ))) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  have hB : 0 ≤ CK + Ci + CQ := by linarith
  obtain ⟨C, hC, hdiag⟩ := i3PsiPairing_bound_uniform (B := CK + Ci + CQ) hB hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hz hz' hzz hz1 hz1'
  rw [hairerI3PsiField_integral_mul_eq_pairing N hρ hε.1 hW hξ x y y']
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ (CK + Ci + CQ) * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerKernelTorus N (u + h) - hairerKernelTorus N u| ≤
          (CK + Ci + CQ) * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) :=
    fun u h hu hh => (hi hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hQ' : ∀ z, 0 < torusParabolicSize z →
      |hairerCovariance N ρ ε z| ≤ (CK + Ci + CQ) * torusParabolicSize z ^ (-(1 : ℝ)) :=
    fun z hz => (hQ hε.1 hε.2 z hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  have := (hdiag (measurable_constantsComparison_hairerKernelTorus N)
    (fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz) hK' hinc'
    (constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2) hQ' (y - x) (y' - x)
    hz hz' hzz' hz1 hz1').2
  rwa [sub_sub_sub_cancel_right] at this

end RegularityStructures.Phi43

end
