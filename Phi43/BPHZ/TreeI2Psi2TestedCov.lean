/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldCov
public import Phi43.BPHZ.TreeI2Psi2DiagramChaosFour
public import Phi43.BPHZ.TreeI2Psi2DiagramChaosTwo
public import Phi43.BPHZ.TreeI2Psi2DiagramZero
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.BPHZ.HairerKernelIncrementTorus
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.Stochastic.ConstantsComparisonC2Bounds

/-!
# The pointwise covariance bound for the field of `I(Ψ²) Ψ²`

By `hairerI2Psi2Field_integral_mul` the covariance `E[F_x(y) F_x(ȳ)]` is the sum of the chaos-`4`
integral, the chaos-`2` integral and the product of the two means.  With `K = hairerKernelTorus N`
and `Q = hairerCovariance N ρ ε` these are exactly the integrals bounded by
`integrable_and_abs_integral_chaos4_le`, `_chaos2_le` and `_chaos0_le`; the constant `B` in their
hypotheses is independent of `ε ∈ (0, 1]` and `x` (`hairerCovariance_abs_le`).  The result is
[Hai14, (10.39)-(10.42)]: for `s(y - x), s(ȳ - x) ≤ 1`, with `d = s(y - ȳ)`, `r = s(y - x)`,
`r' = s(ȳ - x)`,
`|E[F_x(y) F_x(ȳ)]| ≤ C (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)) + r^a r'^a d^(-1) +
  r^(-2δ) + r'^(-2δ))`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Pointwise covariance bound for the field of `I(Ψ²) Ψ²`**, uniform in `ε ∈ (0, 1]` and the
base point `x`. -/
theorem hairerI2Psi2Field_cov_bound (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') → torusParabolicSize (y - x) ≤ 1 →
        torusParabolicSize (y' - x) ≤ 1 →
          |∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y' ∂P| ≤
            C * (torusParabolicSize (y - y') ^ (-δ) + torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
                (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ)) +
              torusParabolicSize (y - x) ^ a * torusParabolicSize (y' - x) ^ a *
                torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
              (torusParabolicSize (y - x) ^ (-(2 * δ)) +
                torusParabolicSize (y' - x) ^ (-(2 * δ)))) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  have hB : 0 ≤ CK + Ci + CQ := by linarith
  obtain ⟨C4, hC4, h4⟩ := integrable_and_abs_integral_chaos4_le hδ hδ1
  obtain ⟨C2, hC2, h2⟩ := integrable_and_abs_integral_chaos2_le ha ha2
  obtain ⟨C0, hC0, h0⟩ := integrable_and_abs_integral_chaos0_le hδ (by linarith)
  set B := CK + Ci + CQ with hBdef
  refine ⟨(C4 + C2 + C0 ^ 2) * B ^ 6, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hr hr' hd hr1 hr1'
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerKernelTorus N (u + h) - hairerKernelTorus N u| ≤
          B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) :=
    fun u h hu hh => (hi hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hQ' : ∀ z, 0 < torusParabolicSize z →
      |hairerCovariance N ρ ε z| ≤ B * torusParabolicSize z ^ (-(1 : ℝ)) :=
    fun z hz => (hQ hε.1 hε.2 z hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hKm := measurable_constantsComparison_hairerKernelTorus N
  have hKs := fun (z : SpaceTime) (hz : 1 < |z.1|) => hairerKernelTorus_eq_zero_of_one_lt_time N hz
  have hQm := constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2
  obtain ⟨-, b4⟩ := h4 hB hKm hQm hKs hK' hinc' hQ' x y y' hr hr1 hr' hr1' hd
  obtain ⟨-, b2⟩ := h2 hB hKm hQm hKs hK' hinc' hQ' x y y' hr hr1 hr' hr1' hd
  obtain ⟨-, bm⟩ := h0 hB hKm hQm hKs hK' hQ' x y (abs_le_one_of_torusParabolicSize_le_one hr1) hr
  obtain ⟨-, bm'⟩ := h0 hB hKm hQm hKs hK' hQ' x y' (abs_le_one_of_torusParabolicSize_le_one hr1') hr'
  obtain ⟨-, heq⟩ := hairerI2Psi2Field_integral_mul N hρ hε.1 hε.1 hW hξ hξ x y y'
  rw [heq]
  have e4 : (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 *
      hairerI2Psi2Kernel N x y' q.2 * hairerI2Psi2Chaos4 N ρ ε ε ε ε y y' q.1 q.2) =
      ∫ q : SpaceTime × SpaceTime, i2Psi2Increment (hairerKernelTorus N) x y q.1 *
        i2Psi2Increment (hairerKernelTorus N) x y' q.2 *
          (4 * hairerCovariance N ρ ε (q.1 - q.2) ^ 2 * hairerCovariance N ρ ε (y - y') ^ 2 +
            4 * hairerCovariance N ρ ε (q.1 - y') ^ 2 * hairerCovariance N ρ ε (y - q.2) ^ 2 +
              16 * (hairerCovariance N ρ ε (q.1 - q.2) * hairerCovariance N ρ ε (q.1 - y') *
                hairerCovariance N ρ ε (y - q.2) * hairerCovariance N ρ ε (y - y'))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hairerI2Psi2Chaos4, hairerWickSquareFourChaos4, hairerCrossCovariance_self,
      hairerI2Psi2Kernel, i2Psi2Increment]
  have e2 : (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 *
      hairerI2Psi2Kernel N x y' q.2 * hairerI2Psi2Chaos2 N ρ ε ε ε ε y y' q.1 q.2) =
      ∫ q : SpaceTime × SpaceTime, i2Psi2Increment (hairerKernelTorus N) x y q.1 *
        i2Psi2Increment (hairerKernelTorus N) x y' q.2 *
          (16 * hairerCovariance N ρ ε (q.1 - y) * hairerCovariance N ρ ε (q.2 - y') *
            (hairerCovariance N ρ ε (q.1 - q.2) * hairerCovariance N ρ ε (y - y') +
              hairerCovariance N ρ ε (q.1 - y') * hairerCovariance N ρ ε (y - q.2))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hairerI2Psi2Chaos2, hairerWickSquareFourChaos2, hairerCrossCovariance_self,
      hairerI2Psi2Kernel, i2Psi2Increment]
  rw [e4, e2]
  set d := torusParabolicSize (y - y')
  set r := torusParabolicSize (y - x)
  set r' := torusParabolicSize (y' - x)
  have nr : ∀ (u e : ℝ), 0 < u → 0 ≤ u ^ e := fun u e hu => Real.rpow_nonneg hu.le e
  have hu : r ^ (-δ) * r ^ (-δ) = r ^ (-(2 * δ)) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hv : r' ^ (-δ) * r' ^ (-δ) = r' ^ (-(2 * δ)) := by
    rw [← Real.rpow_add hr']; congr 1; ring
  have hamgm : r ^ (-δ) * r' ^ (-δ) ≤ r ^ (-(2 * δ)) + r' ^ (-(2 * δ)) := by
    rw [← hu, ← hv]
    linarith only [sq_nonneg (r ^ (-δ) - r' ^ (-δ)), mul_nonneg (nr r (-δ) hr) (nr r' (-δ) hr')]
  have hmm : |(-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2) *
      (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y') ^ 2)| ≤
      C0 ^ 2 * B ^ 6 * (r ^ (-(2 * δ)) + r' ^ (-(2 * δ))) := by
    rw [abs_mul]
    calc _ ≤ (C0 * B ^ 3 * r ^ (-δ)) * (C0 * B ^ 3 * r' ^ (-δ)) :=
          mul_le_mul bm bm' (abs_nonneg _) (by have := nr r (-δ) hr; positivity)
      _ = C0 ^ 2 * B ^ 6 * (r ^ (-δ) * r' ^ (-δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hamgm (by positivity)
  have X4 : 0 ≤ d ^ (-δ) + d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) := by
    have := nr d (-δ) hd; have := nr d (-(2 : ℝ)) hd; have := nr r (2 - δ) hr
    have := nr r' (2 - δ) hr'
    positivity
  have X2 : 0 ≤ r ^ a * r' ^ a * d ^ (-(1 : ℝ)) := by
    have := nr d (-(1 : ℝ)) hd; have := nr r a hr; have := nr r' a hr'
    positivity
  have X0 : 0 ≤ r ^ (-(2 * δ)) + r' ^ (-(2 * δ)) := by
    have := nr r (-(2 * δ)) hr; have := nr r' (-(2 * δ)) hr'
    positivity
  generalize d ^ (-δ) + d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) = Y4 at X4 b4 ⊢
  generalize r ^ a * r' ^ a * d ^ (-(1 : ℝ)) = Y2 at X2 b2 ⊢
  generalize r ^ (-(2 * δ)) + r' ^ (-(2 * δ)) = Y0 at X0 hmm ⊢
  generalize hI4 : ∫ q : SpaceTime × SpaceTime, i2Psi2Increment (hairerKernelTorus N) x y q.1 *
        i2Psi2Increment (hairerKernelTorus N) x y' q.2 *
          (4 * hairerCovariance N ρ ε (q.1 - q.2) ^ 2 * hairerCovariance N ρ ε (y - y') ^ 2 +
            4 * hairerCovariance N ρ ε (q.1 - y') ^ 2 * hairerCovariance N ρ ε (y - q.2) ^ 2 +
              16 * (hairerCovariance N ρ ε (q.1 - q.2) * hairerCovariance N ρ ε (q.1 - y') *
                hairerCovariance N ρ ε (y - q.2) * hairerCovariance N ρ ε (y - y')))
    = I4 at b4 ⊢
  generalize hI2 : ∫ q : SpaceTime × SpaceTime, i2Psi2Increment (hairerKernelTorus N) x y q.1 *
        i2Psi2Increment (hairerKernelTorus N) x y' q.2 *
          (16 * hairerCovariance N ρ ε (q.1 - y) * hairerCovariance N ρ ε (q.2 - y') *
            (hairerCovariance N ρ ε (q.1 - q.2) * hairerCovariance N ρ ε (y - y') +
              hairerCovariance N ρ ε (q.1 - y') * hairerCovariance N ρ ε (y - q.2))) = I2 at b2 ⊢
  generalize (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2) *
      (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y') ^ 2) = M0 at hmm ⊢
  have hB6 : 0 ≤ B ^ 6 := by positivity
  have s4 : C4 * B ^ 6 * Y4 ≤ C4 * B ^ 6 * (Y4 + Y2 + Y0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have s2 : C2 * B ^ 6 * Y2 ≤ C2 * B ^ 6 * (Y4 + Y2 + Y0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have s0 : C0 ^ 2 * B ^ 6 * Y0 ≤ C0 ^ 2 * B ^ 6 * (Y4 + Y2 + Y0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have tri := abs_add_three I4 I2 M0
  linarith [tri, b4, b2, hmm, s4, s2, s0]

end RegularityStructures.Phi43

end
