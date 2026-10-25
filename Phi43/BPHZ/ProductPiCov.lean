/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldMoment
public import Phi43.BPHZ.ProductDiagramI2Psi
public import Phi43.BPHZ.TreeI3PsiTestedPairing

/-!
# The pointwise covariance bound for `I₂Ψ`

The covariance `E[I₂Ψ_x(y) I₂Ψ_x(ȳ)]` equals the diagram `∫∫ isqDiagramIntegrand` with the gain
kernels `K(y - x - ·) - K(-·)` and `Q = hairerCovariance N ρ ε`, and `isqPairing_bound` gives, for
`θ ∈ (0, 1)`, `η ∈ (0, 1/2)`, uniformly in `ε ∈ (0, 1]` and the base point,
`|E[I₂Ψ_x(y) I₂Ψ_x(ȳ)]| ≤ C (1 + s(y - x)²) (s(y - ȳ)^(-1) (s(y - x)^θ s(ȳ - x)^θ) +
  s(y - x)^η s(ȳ - x)^η)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Kernel data.**  There is `B` such that the recentred kernels `K(z - ·) - K(-·)` are gain
kernels with constant `12 B`, `Θ = 1`, and every `Q_ε`, `ε ∈ (0, 1]`, is a propagator kernel. -/
theorem productKernelData (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ z : SpaceTime, IsGainKernel 1 (12 * B) (|z.1| + 1) z
        (fun w => hairerKernelTorus N (z - w) - hairerKernelTorus N (-w))) ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → IsPropKernel B (hairerCovariance N ρ ε) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  have hB : 0 ≤ CK + Ci + CQ := by linarith
  refine ⟨CK + Ci + CQ, hB, ?_, ?_⟩
  · intro z
    refine isGainKernel_dK hB (measurable_constantsComparison_hairerKernelTorus N)
      (fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz) ?_ ?_ z
    · intro z hz
      exact (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    · intro u h hu hh
      exact (hi hu hh).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  · intro ε hε hε1
    refine ⟨constantsComparison_hairerCovariance_measurable N ρ hε hρ hε1, hB, ?_⟩
    intro z hz
    exact (hQ hε hε1 z hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- Translating the integration variables by the base point `x`. -/
theorem productISqPsiField_integral_mul_eq_pairing (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : SpaceTime) :
    ∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' ∂P =
      ∫ a, ∫ b, isqDiagramIntegrand
        (fun w => hairerKernelTorus N (y - x - w) - hairerKernelTorus N (-w))
        (fun w => hairerKernelTorus N (y' - x - w) - hairerKernelTorus N (-w))
        (hairerCovariance N ρ ε) (y - x) (y' - x) a b := by
  rw [productISqPsiField_integral_mul_two_scale N hρ hε hε hW hξ hξ x x y y']
  have key : ∀ H : SpaceTime → SpaceTime → ℝ,
      ∫ w, ∫ w', H w w' = ∫ a, ∫ b, H (x + a) (x + b) := by
    intro H
    rw [← integral_comp_add_left_spaceTime (fun w => ∫ w', H w w') x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact (integral_comp_add_left_spaceTime (fun w' => H (x + a) w') x).symm
  rw [key]
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
  have e10 : y - (x + b) = y - x - b := by abel
  simp only [isqBlockKernel, isqDiagramIntegrand, hairerCrossCovariance_self, hairerI2Psi2Kernel,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  ring

/-- **Pointwise covariance bound for `I₂Ψ`**, uniform in `ε ∈ (0, 1]` and the base point. -/
theorem productISqPsiField_cov_bound (N : ℕ) (hρ : IsMollifier ρ) {θ η : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - y') →
        |∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' ∂P| ≤
          C * (1 + torusParabolicSize (y - x) ^ 2) *
            (torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
              (torusParabolicSize (y - x) ^ θ * torusParabolicSize (y' - x) ^ θ) +
              torusParabolicSize (y - x) ^ η * torusParabolicSize (y' - x) ^ η) := by
  obtain ⟨B, hB, hG, hQ⟩ := productKernelData N hρ
  obtain ⟨C, hC, hdiag⟩ := isqPairing_bound (Θ := 1) hθ0 hθ1 hθ1.le hη0 hη1 (by linarith)
  refine ⟨C * ((12 * B) * (12 * B) * B ^ 3) * 2, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hzz
  rw [productISqPsiField_integral_mul_eq_pairing N hρ hε.1 hW hξ x y y']
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  have hga := hG (y - x)
  have hgb := hG (y' - x)
  have hga' : IsGainKernel 1 (12 * B) (|(y - x).1| + 1) (y - x)
      (fun w => hairerKernelTorus N (y - x - w) - hairerKernelTorus N (-w)) := hga
  have hgb' : IsGainKernel 1 (12 * B) (|(y' - x).1| + 1) (y' - x)
      (fun w => hairerKernelTorus N (y' - x - w) - hairerKernelTorus N (-w)) := hgb
  have := (hdiag (by positivity) (by positivity) hga' hgb' (hQ hε.1 hε.2) (by positivity)
    hzz').2
  rw [sub_sub_sub_cancel_right] at this
  refine this.trans ?_
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  set S : ℝ := torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
      (torusParabolicSize (y - x) ^ θ * torusParabolicSize (y' - x) ^ θ) +
      torusParabolicSize (y - x) ^ η * torusParabolicSize (y' - x) ^ η with hSdef
  have rp : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg u) e
  have hS : 0 ≤ S := by
    rw [hSdef]
    exact add_nonneg (mul_nonneg (rp _ _) (mul_nonneg (rp _ _) (rp _ _)))
      (mul_nonneg (rp _ _) (rp _ _))
  have hT : 1 + (|(y - x).1| + 1) ≤ 2 * (1 + torusParabolicSize (y - x) ^ 2) := by
    nlinarith [sq_nonneg (torusParabolicSize (y - x))]
  have hK : 0 ≤ C * ((12 * B) * (12 * B) * B ^ 3) := by positivity
  calc C * (12 * B * (12 * B) * B ^ 3) * (1 + (|(y - x).1| + 1)) * S
      ≤ C * (12 * B * (12 * B) * B ^ 3) * (2 * (1 + torusParabolicSize (y - x) ^ 2)) * S := by
        gcongr
    _ = _ := by ring

end RegularityStructures.Phi43

end
