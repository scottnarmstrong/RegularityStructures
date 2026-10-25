/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2TestedPeriodise
public import Phi43.BPHZ.TreeI3Psi2TestedSize
public import Phi43.BPHZ.KernelCalculusBasic
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Phi43.Stochastic.ConstantsComparisonLocalSingular
public import Phi43.Stochastic.ConstantsComparisonPeriodise
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.Stochastic.ConstantsComparisonDefinitions

/-!
# Increment of the mollified Hairer kernel near the singularity

For `J = hairerMollifiedKernel N ρ ε` and `P = ρ_ε^♯`, `J(u + h) - J(u) = ∫ K(u - w) (P(w + h) - P(w)) dw`.
When `s(u) ≤ 2 B ε` (`B` the support radius of `P` in units of `ε`) and `s(h) ≤ s(u)/4`, the
difference of `P` is supported in `{s(w) ≤ 2 B ε}` and bounded by `C ε⁻⁶ s(h)`, so that
`|J(u + h) - J(u)| ≤ C s(h) ε⁻⁴ ≤ C' s(h) s(u)⁻⁴`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The local mass of `|K|` in a parabolic ball is at most `C r²` (cf. the same estimate in
`ConstantsComparisonHairerMollifiedBound`, which is private). -/
theorem hairerKernelTorus_ball_integral_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, 0 < r → ∀ {z : SpaceTime}, torusParabolicSize z ≤ r →
      ∫ w in {w : SpaceTime | torusParabolicSize w ≤ r}, |hairerKernelTorus N (z - w)| ≤
        C * r ^ 2 := by
  obtain ⟨C, hC, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  refine ⟨C * 160, by positivity, ?_⟩
  intro r hr z hz
  set S : Set SpaceTime := {w : SpaceTime | torusParabolicSize w ≤ r} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hKshift : Integrable (fun w : SpaceTime => |hairerKernelTorus N (z - w)|) :=
    (integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) z).norm
  have h2r : 0 < 2 * r := by positivity
  have hweight : Integrable (fun w : SpaceTime =>
      C * constantsComparisonLocalSingularWeight (2 * r) (z - w)) :=
    (integrable_comp_sub_left_spaceTime
      (integrable_constantsComparisonLocalSingularWeight h2r).1 z).const_mul C
  have hne : ∀ᵐ w : SpaceTime ∂volume, w ≠ z := by
    exact @Measure.ae_ne SpaceTime _ volume (Measure.IsAddHaarMeasure.nullSingletonClass volume) z
  have hpoint : ∀ᵐ w : SpaceTime ∂volume, S.indicator
      (fun w : SpaceTime => |hairerKernelTorus N (z - w)|) w ≤
        C * constantsComparisonLocalSingularWeight (2 * r) (z - w) := by
    filter_upwards [hne] with w hw
    by_cases hws : w ∈ S
    · have hzw : torusParabolicSize (z - w) ≤ 2 * r := by
        have := torusParabolicSize_sub_le_add_self z w
        have hws' : torusParabolicSize w ≤ r := hws
        linarith
      have hzpos : 0 < torusParabolicSize (z - w) :=
        torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm hw))
      rw [Set.indicator_of_mem hws]
      have := hK hzpos
      simpa [constantsComparisonLocalSingularWeight, hzpos, hzw] using this
    · rw [Set.indicator_of_notMem hws]
      exact mul_nonneg hC (nonneg_constantsComparisonLocalSingularWeight _ _)
  have hmono := integral_mono_ae (hKshift.indicator hS) hweight hpoint
  calc ∫ w in S, |hairerKernelTorus N (z - w)|
      = ∫ w, S.indicator (fun w : SpaceTime => |hairerKernelTorus N (z - w)|) w := by
        rw [integral_indicator hS]
    _ ≤ ∫ w, C * constantsComparisonLocalSingularWeight (2 * r) (z - w) := hmono
    _ = C * ∫ w, constantsComparisonLocalSingularWeight (2 * r) w := by
        rw [integral_const_mul, integral_comp_sub_left_spaceTime]
    _ ≤ C * (40 * (2 * r) ^ 2) := by
        gcongr
        exact integral_constantsComparisonLocalSingularWeight_le h2r
    _ = C * 160 * r ^ 2 := by ring

/-- `J(u + h) - J(u) = ∫ K(u - w) (P(w + h) - P(w)) dw`. -/
theorem hairerMollifiedKernel_add_sub_eq (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (u h : SpaceTime) :
    hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u =
      ∫ w, hairerKernelTorus N (u - w) * (periodise ρ ε (w + h) - periodise ρ ε w) := by
  obtain ⟨D, hD⟩ := bounded_periodise ρ hρ hε
  have hKi : Integrable (fun w : SpaceTime => hairerKernelTorus N (u - w)) :=
    integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) u
  have hPm : Measurable (periodise ρ ε) := measurable_periodise ρ hρ
  have i1 : Integrable (fun w : SpaceTime => hairerKernelTorus N (u - w) *
      periodise ρ ε (w + h)) :=
    hKi.mul_bdd (c := D) (hPm.comp (measurable_id.add_const h)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hD _)
  have i0 : Integrable (fun w : SpaceTime => hairerKernelTorus N (u - w) * periodise ρ ε w) :=
    hKi.mul_bdd (c := D) hPm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hD _)
  have e : ∀ w : SpaceTime, hairerKernelTorus N (u - w) * (periodise ρ ε (w + h) -
      periodise ρ ε w) = hairerKernelTorus N (u - w) * periodise ρ ε (w + h) -
        hairerKernelTorus N (u - w) * periodise ρ ε w := fun w => by ring
  simp only [e]
  rw [integral_sub i1 i0]
  unfold hairerMollifiedKernel
  congr 1
  rw [← integral_add_right_eq_self (fun w : SpaceTime => hairerKernelTorus N (u + h - w) *
    periodise ρ ε w) h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [add_sub_add_right_eq_sub]

/-- **Increment of `J_ε` near the singularity** (`s(u) ≤ 2 B ε`, `s(h) ≤ s(u)/4`). -/
theorem hairerMollifiedKernel_increment_near (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {B : ℝ} (hB : 0 < B)
    (hsupp : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ w : SpaceTime,
      periodise ρ ε w ≠ 0 → torusParabolicSize w ≤ B * ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {u h : SpaceTime},
      0 < torusParabolicSize u → torusParabolicSize u ≤ 2 * B * ε →
      torusParabolicSize h ≤ torusParabolicSize u / 4 →
        |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
          C * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
  obtain ⟨Cp, hCp, hP⟩ := periodise_sub_abs_le_uniform ρ hρ
  obtain ⟨Cb, hCb, hball⟩ := hairerKernelTorus_ball_integral_le N
  refine ⟨Cp * Cb * (2 * B) ^ 2 * (2 * B) ^ 4, by positivity, ?_⟩
  intro ε hε hε1 u h hu huε hh
  set r : ℝ := 2 * B * ε with hr
  have hr0 : 0 < r := by positivity
  set S : Set SpaceTime := {w : SpaceTime | torusParabolicSize w ≤ r} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hKi : Integrable (fun w : SpaceTime => |hairerKernelTorus N (u - w)|) :=
    (integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) u).norm
  set M : ℝ := Cp * ε ^ (-6 : ℤ) * torusParabolicSize h with hM
  have hM0 : 0 ≤ M := by
    have := zpow_pos hε (-6 : ℤ)
    have := torusParabolicSize_nonneg h
    positivity
  have hmaj : Integrable (fun w : SpaceTime => M * S.indicator
      (fun w : SpaceTime => |hairerKernelTorus N (u - w)|) w) := (hKi.indicator hS).const_mul M
  rw [hairerMollifiedKernel_add_sub_eq N hρ hε]
  have hpt : ∀ w : SpaceTime, ‖hairerKernelTorus N (u - w) *
      (periodise ρ ε (w + h) - periodise ρ ε w)‖ ≤
        M * S.indicator (fun w : SpaceTime => |hairerKernelTorus N (u - w)|) w := by
    intro w
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw]
      calc |hairerKernelTorus N (u - w)| * |periodise ρ ε (w + h) - periodise ρ ε w|
          ≤ |hairerKernelTorus N (u - w)| * M :=
            mul_le_mul_of_nonneg_left (hP hε hε1 w h) (abs_nonneg _)
        _ = M * |hairerKernelTorus N (u - w)| := mul_comm _ _
    · rw [Set.indicator_of_notMem hw, mul_zero]
      have h0 : periodise ρ ε w = 0 := by
        by_contra hne
        exact hw (le_trans (hsupp hε hε1 w hne) (by rw [hr]; nlinarith))
      have h1 : periodise ρ ε (w + h) = 0 := by
        by_contra hne
        apply hw
        have h2 := hsupp hε hε1 (w + h) hne
        have h3 := torusParabolicSize_sub_le_add_self (w + h) h
        rw [add_sub_cancel_right] at h3
        show torusParabolicSize w ≤ r
        rw [hr]
        nlinarith
      rw [h0, h1]
      simp
  refine (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)).trans ?_
  have hint : ∫ w, M * S.indicator (fun w : SpaceTime => |hairerKernelTorus N (u - w)|) w ≤
      M * (Cb * r ^ 2) := by
    rw [integral_const_mul, integral_indicator hS]
    exact mul_le_mul_of_nonneg_left (hball hr0 (by rw [hr]; nlinarith)) hM0
  refine hint.trans ?_
  -- algebra: `M * Cb * r² = Cp * Cb * (2B)² * s(h) * ε⁻⁴`, and `ε⁻¹ ≤ 2B / s(u)`
  have hinv : ε⁻¹ ≤ 2 * B * torusParabolicSize u ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hu, inv_mul_eq_div, div_le_iff₀ hε]
    linarith
  have h4 : ε ^ (-4 : ℤ) ≤ (2 * B) ^ 4 * torusParabolicSize u ^ (-(4 : ℝ)) := by
    have e1 : ε ^ (-4 : ℤ) = (ε⁻¹) ^ 4 := by rw [zpow_neg, ← inv_zpow]; norm_cast
    have e2 : torusParabolicSize u ^ (-(4 : ℝ)) = (torusParabolicSize u ^ (-(1 : ℝ))) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
    rw [e1, e2, ← mul_pow]
    exact pow_le_pow_left₀ (inv_pos.2 hε).le hinv 4
  have e3 : M * (Cb * r ^ 2) = Cp * Cb * (2 * B) ^ 2 * torusParabolicSize h * ε ^ (-4 : ℤ) := by
    rw [hM, hr, show (-4 : ℤ) = -6 + 2 by norm_num, zpow_add₀ hε.ne',
      show ε ^ (2 : ℤ) = ε ^ 2 by norm_cast]
    ring
  rw [e3]
  have hs0 := torusParabolicSize_nonneg h
  calc Cp * Cb * (2 * B) ^ 2 * torusParabolicSize h * ε ^ (-4 : ℤ)
      ≤ Cp * Cb * (2 * B) ^ 2 * torusParabolicSize h *
        ((2 * B) ^ 4 * torusParabolicSize u ^ (-(4 : ℝ))) := by gcongr
    _ = _ := by ring

end RegularityStructures.Phi43

end
