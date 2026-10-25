/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Cov
public import Phi43.BPHZ.TreeI2Psi2TestedCov
public import Phi43.BPHZ.TreeI3Psi2ChaosOneBasic

/-!
# The global covariance bound for the field of `I(Ψ²) Ψ²`

`hairerI2Psi2Field_cov_bound_global`: for all `x, y, y'` with `y, y' ≠ x` and `y ≠ y'`, uniformly in
`ε ∈ (0, 1]`,
`|E[F_x(y) F_x(y')]| ≤ C (1 + s(y - x)² + s(y' - x)²)³
  (s(y - y')^(-2) + s(y - y')^(-1) + s(y - y')^(-1/2) + s(y - x)^(-1/2) + s(y' - x)^(-1/2))`.
There is no restriction `s(y - x), s(y' - x) ≤ 1`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The covariance of the field of `I(Ψ²) Ψ²` is `i2Psi2CovAbs` for the kernel and covariance of
the regularised noise. -/
theorem hairerI2Psi2Field_integral_mul_eq_covAbs {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ξ : Ω → SpaceTime → ℝ} (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : SpaceTime) :
    ∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y' ∂P =
      i2Psi2CovAbs (hairerKernelTorus N) (hairerCovariance N ρ ε) x y y' := by
  obtain ⟨-, heq⟩ := hairerI2Psi2Field_integral_mul N hρ hε hε hW hξ hξ x y y'
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
  rfl

/-- **Global covariance bound for the field of `I(Ψ²) Ψ²`**, uniform in `ε ∈ (0, 1]` and the base
point. -/
theorem hairerI2Psi2Field_cov_bound_global (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y * hairerI2Psi2Field N ρ ε ξ x ω y' ∂P| ≤
            C * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 *
              (torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
                torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) +
                torusParabolicSize (y - x) ^ (-(1 / 2 : ℝ)) +
                torusParabolicSize (y' - x) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨CQ, hCQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  have hB : 0 ≤ CK + CQ := by linarith
  obtain ⟨C0, hC0, hbd⟩ := i2Psi2CovAbs_bound_global hB
  refine ⟨250 * C0, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hr hr' hd
  have hdata : SingularKernelData (hairerKernelTorus N) (hairerCovariance N ρ ε) (CK + CQ) :=
    { nonneg := hB
      measurable_K := measurable_constantsComparison_hairerKernelTorus N
      measurable_Q := constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2
      K_bound := fun z hz => (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      K_supp := fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz
      Q_bound := fun z hz => (hQ hε.1 hε.2 z hz).trans (mul_le_mul_of_nonneg_right
        (by linarith) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) }
  rw [hairerI2Psi2Field_integral_mul_eq_covAbs N hρ hε.1 hW hξ x y y']
  have hxy : 0 < torusParabolicSize (x - y) := torusParabolicSize_sub_pos_symm hr
  have hxy' : 0 < torusParabolicSize (x - y') := torusParabolicSize_sub_pos_symm hr'
  set t : ℝ := |y.1 - x.1| with ht
  set t' : ℝ := |y'.1 - x.1| with ht'
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht0' : 0 ≤ t' := abs_nonneg _
  have hT0 : 0 ≤ 2 * (t + t' + 2) := by positivity
  have hD : ∀ a b : SpaceTime, |a.1 - x.1| ≤ t + t' + 2 → |b.1 - x.1| ≤ t + t' + 2 →
      torusParabolicSize (a - b) ≤ √(2 * (t + t' + 2)) + 1 := by
    intro a b ha hb
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (a - b).1 = a.1 - b.1 := rfl
    rw [this]
    have h1 : |a.1 - b.1| ≤ |a.1 - x.1| + |b.1 - x.1| := by
      calc |a.1 - b.1| = |(a.1 - x.1) - (b.1 - x.1)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  have key := hbd hdata x y y' (D := √(2 * (t + t' + 2)) + 1) (by positivity) hD hd hxy hxy'
  refine key.trans ?_
  -- compare the prefactors and the singular sums
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e2 := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hpoly := poly_prefactor_le ht0 ht0' (a := torusParabolicSize (y - x) ^ 2)
    (b := torusParabolicSize (y' - x) ^ 2) e1 e2
  have f1 : torusParabolicSize (x - y) ^ (-(1 / 2 : ℝ)) ≤ 2 * torusParabolicSize (y - x) ^ (-(1 / 2 : ℝ)) :=
    torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := 1 / 2) (by norm_num) (by norm_num) hr
  have f2 : torusParabolicSize (x - y') ^ (-(1 / 2 : ℝ)) ≤
      2 * torusParabolicSize (y' - x) ^ (-(1 / 2 : ℝ)) :=
    torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := 1 / 2) (by norm_num) (by norm_num) hr'
  have nn : ∀ s e : ℝ, 0 ≤ s → 0 ≤ s ^ e := fun s e hs => Real.rpow_nonneg hs e
  have n1 := nn (torusParabolicSize (y - y')) (-(2 : ℝ)) (torusParabolicSize_nonneg _)
  have n2 := nn (torusParabolicSize (y - y')) (-(1 : ℝ)) (torusParabolicSize_nonneg _)
  have n3 := nn (torusParabolicSize (y - y')) (-(1 / 2 : ℝ)) (torusParabolicSize_nonneg _)
  have n4 := nn (torusParabolicSize (y - x)) (-(1 / 2 : ℝ)) (torusParabolicSize_nonneg _)
  have n5 := nn (torusParabolicSize (y' - x)) (-(1 / 2 : ℝ)) (torusParabolicSize_nonneg _)
  have n6 := nn (torusParabolicSize (x - y)) (-(1 / 2 : ℝ)) (torusParabolicSize_nonneg _)
  have n7 := nn (torusParabolicSize (x - y')) (-(1 / 2 : ℝ)) (torusParabolicSize_nonneg _)
  have hS : torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
      torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) + torusParabolicSize (x - y) ^ (-(1 / 2 : ℝ)) +
      torusParabolicSize (x - y') ^ (-(1 / 2 : ℝ)) ≤
      2 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
        torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) + torusParabolicSize (y - x) ^ (-(1 / 2 : ℝ)) +
        torusParabolicSize (y' - x) ^ (-(1 / 2 : ℝ))) := by linarith
  have hfac0 : 0 ≤ (1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t') := by positivity
  calc C0 * ((1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t')) *
        (torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
          torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) + torusParabolicSize (x - y) ^ (-(1 / 2 : ℝ)) +
          torusParabolicSize (x - y') ^ (-(1 / 2 : ℝ)))
      ≤ C0 * (125 * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3) *
        (2 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
          torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) +
          torusParabolicSize (y - x) ^ (-(1 / 2 : ℝ)) +
          torusParabolicSize (y' - x) ^ (-(1 / 2 : ℝ)))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC0) hS (by linarith) (by positivity)
    _ = _ := by ring

end RegularityStructures.Phi43

end
