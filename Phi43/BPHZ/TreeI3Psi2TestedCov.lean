/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2TestedCovIdentity
public import Phi43.BPHZ.TreeI3Psi2TestedJIncrement
public import Phi43.BPHZ.TreeI3Psi2DiagramCov
public import Phi43.BPHZ.TreePsiDifference
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.BPHZ.HairerKernelIncrementTorus
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.Stochastic.ConstantsComparisonC2Bounds
public import Phi43.Stochastic.ConstantsComparisonConvolution

/-!
# The pointwise covariance bound for the field of `I(Ψ³) Ψ²`

By `hairerI3Psi2Field_integral_mul` and `hairerI3Psi2Cov_eq_i3Psi2Cov`, the covariance
`E[F_x(y) F_x(ȳ)]` is the abstract diagram `i3Psi2Cov K Q c (y - x) (ȳ - x)` with
`K = hairerKernelTorus N`, `J = hairerMollifiedKernel N ρ ε`, `Q = hairerCovariance N ρ ε`
(`Q z = ∫ J (z + w) J w dw`, the definition) and `c = hairerSunsetConstant N ρ ε`
(`c = 2 ∫ K Q²`, the definition).  The deterministic bound `i3Psi2Cov_bound_uniform` applies, with
a constant independent of `ε ∈ (0, 1]` and `x`: the singular bound for `J` is uniform in `ε`
since `(s + ε)⁻³ ≤ s⁻³`, and the increment bound for `J` is
`hairerMollifiedKernel_increment_uniform`.  The qualitative hypotheses (`J` bounded, integrable,
measurable) hold for each fixed `ε`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The mollified Hairer kernel is integrable for `ε ∈ (0, 1]`. -/
theorem integrable_hairerMollifiedKernel (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : Integrable (hairerMollifiedKernel N ρ ε) := by
  rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
  exact (integrable_periodise ρ hρ hε).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    (integrable_constantsComparison_hairerKernelTorus N)

/-- **Pointwise covariance bound for the field of `I(Ψ³) Ψ²`**, uniform in `ε ∈ (0, 1]` and the
base point `x` ([Hai14, p. 170--171]).  For `δ ∈ (0, 1/4]`, distinct points `y, ȳ, x` with
`s(y - x), s(ȳ - x) ≤ 1`, `|E[F_x(y) F_x(ȳ)]| ≤ C · i3Psi2Target δ (y - x) (ȳ - x)`. -/
theorem hairerI3Psi2Field_cov_bound (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') → torusParabolicSize (y - x) ≤ 1 →
        torusParabolicSize (y' - x) ≤ 1 →
          |∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y * hairerI3Psi2Field N ρ ε ξ x ω y' ∂P| ≤
            C * i3Psi2Target δ (y - x) (y' - x) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨CJ, hCJ, hJ⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨CI, hCI, hJi⟩ := hairerMollifiedKernel_increment_uniform N hρ
  set B : ℝ := CK + Ci + CQ + CJ + CI with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨C, hC, hdiag⟩ := i3Psi2Cov_bound_uniform hB hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hz hz' hzz hz1 hz1'
  have hprob := hW.isProbabilityMeasure
  rw [(hairerI3Psi2Field_integral_mul N hρ hε.1 hε.1 hW hξ hξ x y y').2]
  change |hairerI3Psi2Cov N ρ x ε ε y y'| ≤ _
  rw [hairerI3Psi2Cov_eq_i3Psi2Cov]
  have hrp : ∀ z : SpaceTime, 0 ≤ torusParabolicSize z ^ (-(3 : ℝ)) :=
    fun z => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK hz).trans (mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (hrp z))
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerKernelTorus N (u + h) - hairerKernelTorus N u| ≤
          B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) :=
    fun u h hu hh => (hi hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hQ' : ∀ z, 0 < torusParabolicSize z →
      |hairerCovariance N ρ ε z| ≤ B * torusParabolicSize z ^ (-(1 : ℝ)) :=
    fun z hz => (hQ hε.1 hε.2 z hz).trans (mul_le_mul_of_nonneg_right
      (by rw [hBdef]; linarith) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hJ' : ∀ z, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := by
    intro z hz
    refine (hJ hε.1 hε.2 z).trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz (by linarith [hε.1])
      (by norm_num)) hCJ).trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (hrp z)
  have hJinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
          B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) :=
    fun u h hu hh => (hJi hε.1 hε.2 u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hJb : ∀ z, |hairerMollifiedKernel N ρ ε z| ≤ CJ * ε ^ (-(3 : ℝ)) := by
    intro z
    refine (hJ hε.1 hε.2 z).trans (mul_le_mul_of_nonneg_left ?_ hCJ)
    exact Real.rpow_le_rpow_of_nonpos hε.1 (by linarith [torusParabolicSize_nonneg z])
      (by norm_num)
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by
    rwa [sub_sub_sub_cancel_right]
  exact hdiag (measurable_constantsComparison_hairerKernelTorus N)
    (fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz) hK' hinc'
    (measurable_hairerMollifiedKernel N hρ ε) hJ' hJinc' hJb
    (integrable_hairerMollifiedKernel N ρ hρ hε.1)
    (constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2) hQ' (fun x => rfl) rfl
    (y - x) (y' - x) hz hz' hzz' hz1 hz1'

end RegularityStructures.Phi43

end
