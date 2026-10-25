/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Cov
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Alg
public import Phi43.BPHZ.TreeI3Psi2TestedCov
public import Phi43.BPHZ.TreeI3Psi2ChaosOneBasic

/-!
# The global covariance bound for the field of `I(Ψ³)Ψ²`

`hairerI3Psi2Field_cov_bound_global`: for all `x, y, y'` with `y, y' ≠ x` and `y ≠ y'`, uniformly in
`ε ∈ (0, 1]`,
`|E[F_x(y) F_x(y')]| ≤ C (1 + s(y - x)² + s(y' - x)²)³ (s(y - y')^(-5/2) + s(y - x)^(-5/2) +
s(y' - x)^(-5/2) + 1)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Global covariance bound for the field of `I(Ψ³)Ψ²`.** -/
theorem hairerI3Psi2Field_cov_bound_global (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y * hairerI3Psi2Field N ρ ε ξ x ω y' ∂P| ≤
            C * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 *
              (torusParabolicSize (y - y') ^ (-(5 / 2 : ℝ)) +
                torusParabolicSize (y - x) ^ (-(5 / 2 : ℝ)) +
                torusParabolicSize (y' - x) ^ (-(5 / 2 : ℝ)) + 1) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨CJ, hCJ, hJ⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨CI, hCI, hJi⟩ := hairerMollifiedKernel_increment_uniform N hρ
  set B : ℝ := CK + CQ + CJ + CI with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨C0, hC0, hbd⟩ := i3Psi2Cov_bound_global hB
  refine ⟨125 * C0, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hz hz' hzz
  have hprob := hW.isProbabilityMeasure
  rw [(hairerI3Psi2Field_integral_mul N hρ hε.1 hε.1 hW hξ hξ x y y').2]
  change |hairerI3Psi2Cov N ρ x ε ε y y'| ≤ _
  rw [hairerI3Psi2Cov_eq_i3Psi2Cov]
  have hrp : ∀ z : SpaceTime, 0 ≤ torusParabolicSize z ^ (-(3 : ℝ)) :=
    fun z => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK hz).trans (mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (hrp z))
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
  set t : ℝ := |(y - x).1| with ht
  set t' : ℝ := |(y' - x).1| with ht'
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht0' : 0 ≤ t' := abs_nonneg _
  have hD : ∀ a b : SpaceTime, |a.1| ≤ t + t' + 2 → |b.1| ≤ t + t' + 2 →
      torusParabolicSize (a - b) ≤ √(2 * (t + t' + 2)) + 1 := by
    intro a b ha hb
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (a - b).1 = a.1 - b.1 := rfl
    rw [this]
    have := abs_sub a.1 b.1
    linarith
  have key := hbd (M := CJ * ε ^ (-(3 : ℝ))) (D := √(2 * (t + t' + 2)) + 1) (by positivity)
    (measurable_constantsComparison_hairerKernelTorus N)
    (fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz) hK'
    (measurable_hairerMollifiedKernel N hρ ε) hJ' hJinc' hJb
    (integrable_hairerMollifiedKernel N ρ hρ hε.1)
    (constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2) hQ' (fun x => rfl) rfl
    (y - x) (y' - x) hD hz hz' hzz'
  refine key.trans ?_
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e2 := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hpoly := poly_prefactor_le ht0 ht0' (a := torusParabolicSize (y - x) ^ 2)
    (b := torusParabolicSize (y' - x) ^ 2) e1 e2
  have hT : 0 ≤ treeTheta (y - x) (y' - x) := treeTheta_nonneg _ _
  have hT' : treeTheta (y - x) (y' - x) = torusParabolicSize (y - y') ^ (-(5 / 2 : ℝ)) +
      torusParabolicSize (y - x) ^ (-(5 / 2 : ℝ)) + torusParabolicSize (y' - x) ^ (-(5 / 2 : ℝ)) +
        1 := by
    unfold treeTheta
    rw [sub_sub_sub_cancel_right]
  rw [hT'] at hT ⊢
  calc C0 * ((1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t')) * _
      ≤ C0 * (125 * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3) *
        _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC0) hT
    _ = _ := by ring

end RegularityStructures.Phi43

end
