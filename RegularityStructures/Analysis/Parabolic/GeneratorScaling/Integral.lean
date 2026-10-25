/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L¹` bounds for rescaled test functions and their generators

The closed unit parabolic ball has volume at most `16` (it lies in `[-1,1]⁴`), so every
`φ ∈ B^r` has `∫ |φ| ≤ 16`, and for `φ ∈ B^4`, `∫ |L φ| ≤ 16 (…)`. We package the hypotheses
of `RegularisingSemigroup.abs_pairing_le` for `φ^c_z` and `L φ^c_z`.
-/

public section

namespace RegularityStructures

open MeasureTheory

/-- The closed parabolic ball of radius `c` about `z`. -/
def closedParabolicBall (z : ParabolicSpace) (c : ℝ) : Set ParabolicSpace :=
  {w | parabolicNorm (w - z) ≤ c}

theorem isClosed_closedParabolicBall (z : ParabolicSpace) (c : ℝ) :
    IsClosed (closedParabolicBall z c) :=
  isClosed_le (continuous_parabolicNorm.comp (continuous_id.sub continuous_const)) continuous_const

theorem abs_fst_le_one {w : ParabolicSpace} (h : parabolicNorm w ≤ 1) : |w.1| ≤ 1 := by
  have h1 : Real.sqrt |w.1| ≤ 1 := by
    have : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold parabolicNorm at h
    linarith
  rw [Real.sqrt_le_left (by norm_num)] at h1
  linarith

theorem abs_snd_le_one {w : ParabolicSpace} (h : parabolicNorm w ≤ 1) (i : Fin 3) :
    |w.2 i| ≤ 1 := by
  have h1 : |w.2 i| ≤ ∑ j, |w.2 j| :=
    Finset.single_le_sum (f := fun j => |w.2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have := Real.sqrt_nonneg |w.1|
  unfold parabolicNorm at h
  linarith

theorem closedParabolicBall_zero_one_subset :
    closedParabolicBall 0 1 ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1 := by
  intro w hw
  have hw' : parabolicNorm w ≤ 1 := by simpa [closedParabolicBall] using hw
  refine ⟨abs_le.1 (abs_fst_le_one hw'), fun i _ => abs_le.1 (abs_snd_le_one hw' i)⟩

theorem isCompact_closedParabolicBall (z : ParabolicSpace) {c : ℝ} (hc : 0 < c) :
    IsCompact (closedParabolicBall z c) := by
  have hK : IsCompact (closedParabolicBall 0 1) :=
    (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)).of_isClosed_subset
      (isClosed_closedParabolicBall 0 1) closedParabolicBall_zero_one_subset
  have himg : closedParabolicBall z c =
      (fun u => parabolicDilate c u + z) '' closedParabolicBall 0 1 := by
    ext w
    constructor
    · intro hw
      refine ⟨parabolicDilate c⁻¹ (w - z), ?_, ?_⟩
      · simp only [closedParabolicBall, Set.mem_ofPred_eq, sub_zero]
        rw [parabolicNorm_parabolicDilate_inv hc, inv_mul_le_iff₀ hc]
        simpa [closedParabolicBall] using hw
      · simp [parabolicDilate_parabolicDilate_inv hc.ne']
    · rintro ⟨u, hu, rfl⟩
      simp only [closedParabolicBall, Set.mem_ofPred_eq, sub_zero] at hu ⊢
      rw [add_sub_cancel_right, parabolicNorm_parabolicDilate hc.le]
      nlinarith
  rw [himg]
  refine hK.image ?_
  unfold parabolicDilate
  fun_prop

theorem volume_closedParabolicBall_zero_one_le :
    volume (closedParabolicBall 0 1) ≤ 16 := by
  refine (measure_mono closedParabolicBall_zero_one_subset).trans ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem hasCompactSupport_of_eq_zero {f : ParabolicSpace → ℝ} {c : ℝ} (hc : 0 < c)
    (z : ParabolicSpace) (hf : ∀ w, c < parabolicNorm (w - z) → f w = 0) : HasCompactSupport f := by
  refine (isCompact_closedParabolicBall z hc).of_isClosed_subset isClosed_closure
    (closure_minimal ?_ (isClosed_closedParabolicBall z c))
  intro w hw
  by_contra h
  exact hw (hf w (not_le.1 h))

theorem hasCompactSupport_of_eq_zero_unit {f : ParabolicSpace → ℝ}
    (hf : ∀ w, 1 < parabolicNorm w → f w = 0) : HasCompactSupport f :=
  hasCompactSupport_of_eq_zero one_pos 0 (by simpa using hf)

theorem integrable_of_continuous_unit {f : ParabolicSpace → ℝ} (hc : Continuous f)
    (hf : ∀ w, 1 < parabolicNorm w → f w = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero_unit hf)

/-- `∫ |f| ≤ 16 B` for a continuous `f` bounded by `B` and vanishing outside the unit ball. -/
theorem integral_abs_le_of_bound {f : ParabolicSpace → ℝ} {B : ℝ} (hc : Continuous f)
    (hf : ∀ w, 1 < parabolicNorm w → f w = 0) (hB : ∀ w, |f w| ≤ B) :
    ∫ w, |f w| ≤ 16 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set S := closedParabolicBall (0 : ParabolicSpace) 1
  have hS : MeasurableSet S := (isClosed_closedParabolicBall 0 1).measurableSet
  have hfin : volume S < ⊤ := lt_of_le_of_lt volume_closedParabolicBall_zero_one_le (by simp)
  have hint : Integrable (fun w => |f w|) := (integrable_of_continuous_unit hc hf).abs
  have hind : Integrable (S.indicator fun _ => B) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hfin.ne)
  have hle : ∀ w, |f w| ≤ S.indicator (fun _ => B) w := by
    intro w
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw]; exact hB w
    · rw [Set.indicator_of_notMem hw, hf w (by simpa [S, closedParabolicBall] using hw)]; simp
  refine (integral_mono hint hind hle).trans ?_
  rw [integral_indicator_const _ hS, smul_eq_mul]
  have h16 : volume.real S ≤ 16 := by
    have := ENNReal.toReal_mono (by simp) volume_closedParabolicBall_zero_one_le
    simpa [Measure.real] using this
  nlinarith

theorem abs_apply_le_one {r : ℕ} {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass r)
    (w : ParabolicSpace) : |φ w| ≤ 1 := by
  simpa using hφ.2.2 0 (Nat.zero_le r) w

/-- `∫ |φ| ≤ 16` for `φ ∈ B^r`. -/
theorem integral_abs_le_of_mem_testFunctionClass {r : ℕ} {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass r) : ∫ w, |φ w| ≤ 16 := by
  simpa using integral_abs_le_of_bound hφ.1.continuous hφ.2.1 (abs_apply_le_one hφ)

/-- `∫ |L φ| ≤ 16 (4π²)⁻¹ + 48 (16π⁴)⁻¹` for `φ ∈ B^4`. -/
theorem integral_abs_parabolicGenerator_le {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) :
    ∫ w, |parabolicGenerator φ w| ≤ 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) :=
  integral_abs_le_of_bound (continuous_parabolicGenerator hφ.1)
    (fun _ hw => parabolicGenerator_eq_zero hφ.2.1 hw) (abs_parabolicGenerator_le hφ)

/-! ### Packaged hypotheses for the bridge -/

theorem contDiff_rescaledTestFunction_of_mem {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) (c : ℝ) (z : ParabolicSpace) :
    ContDiff ℝ (⊤ : ℕ∞) (rescaledTestFunction φ c z) :=
  contDiff_rescaledTestFunction hφ.1 c z

theorem hasCompactSupport_rescaledTestFunction {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    HasCompactSupport (rescaledTestFunction φ c z) :=
  hasCompactSupport_of_eq_zero hc z fun _ h => rescaledTestFunction_eq_zero hφ.2.1 hc h

theorem measurable_rescaledTestFunction {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) (c : ℝ) (z : ParabolicSpace) :
    Measurable (rescaledTestFunction φ c z) :=
  (contDiff_rescaledTestFunction_of_mem hφ c z).continuous.measurable

theorem integrable_rescaledTestFunction {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    Integrable (rescaledTestFunction φ c z) :=
  (contDiff_rescaledTestFunction_of_mem hφ c z).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_rescaledTestFunction hφ hc z)

theorem integral_abs_rescaledTestFunction_le {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    ∫ w, |rescaledTestFunction φ c z w| ≤ 16 := by
  have : ∀ w, |rescaledTestFunction φ c z w| = rescaledTestFunction (fun u => |φ u|) c z w := by
    intro w
    unfold rescaledTestFunction
    rw [abs_mul, abs_of_pos (by positivity)]
  simp_rw [this]
  rw [integral_rescaledTestFunction _ hc]
  exact integral_abs_le_of_mem_testFunctionClass hφ

theorem measurable_parabolicGenerator_rescaledTestFunction {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) (c : ℝ) (z : ParabolicSpace) :
    Measurable (parabolicGenerator (rescaledTestFunction φ c z)) :=
  (continuous_parabolicGenerator (contDiff_rescaledTestFunction_of_mem hφ c z)).measurable

theorem parabolicGenerator_rescaledTestFunction_eq_zero {φ : ParabolicSpace → ℝ} {r : ℕ}
    (hφ : φ ∈ testFunctionClass r) {c : ℝ} (hc : 0 < c) {z w : ParabolicSpace}
    (h : c < parabolicNorm (w - z)) : parabolicGenerator (rescaledTestFunction φ c z) w = 0 := by
  rw [parabolicGenerator_rescaledTestFunction hφ.1 hc, rescaledTestFunction_eq_zero ?_ hc h,
    mul_zero]
  exact fun u hu => parabolicGenerator_eq_zero hφ.2.1 hu

theorem integrable_parabolicGenerator_rescaledTestFunction {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    Integrable (parabolicGenerator (rescaledTestFunction φ c z)) := by
  have hcont := continuous_parabolicGenerator (contDiff_rescaledTestFunction_of_mem hφ c z)
  exact hcont.integrable_of_hasCompactSupport
    (hasCompactSupport_of_eq_zero hc z fun _ h =>
      parabolicGenerator_rescaledTestFunction_eq_zero hφ hc h)

theorem integral_abs_parabolicGenerator_rescaledTestFunction_le {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    ∫ w, |parabolicGenerator (rescaledTestFunction φ c z) w| ≤
      16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * c ^ (-(4 : ℝ)) := by
  have hL : ∀ w, |parabolicGenerator (rescaledTestFunction φ c z) w| =
      (c ^ 4)⁻¹ * rescaledTestFunction (fun u => |parabolicGenerator φ u|) c z w := by
    intro w
    rw [parabolicGenerator_rescaledTestFunction hφ.1 hc, abs_mul, abs_of_pos (by positivity)]
    unfold rescaledTestFunction
    rw [abs_mul, abs_of_pos (by positivity)]
  simp_rw [hL]
  rw [integral_const_mul, integral_rescaledTestFunction _ hc,
    Real.rpow_neg hc.le]
  have := integral_abs_parabolicGenerator_le hφ
  have hp : 0 ≤ (c ^ 4)⁻¹ := by positivity
  have e : c ^ (4 : ℝ) = c ^ 4 := by exact_mod_cast Real.rpow_natCast c 4
  rw [e, mul_comm _ ((c ^ 4)⁻¹)]
  exact mul_le_mul_of_nonneg_left this hp

end RegularityStructures

end
