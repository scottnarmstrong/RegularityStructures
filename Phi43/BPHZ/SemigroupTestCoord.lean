/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestWeighted
public import Phi43.BPHZ.SemigroupTestPeriodiseProfile
public import Phi43.BPHZ.SemigroupTestKernel

/-!
# The coordinate-weighted periodised semigroup kernel is a test profile

`h_i(y) = Q_t(x, y) (y_i - x_i) / lam` with `lam = t^(1/4)` has the periodisation
`semigroupPeriodisedCoord t x i`, which is a `SemigroupTestProfile` at scale `lam` with the moment
function `r ↦ M_{r+1}` (`exists_semigroupTestProfile_semigroupPeriodisedCoord`).  This is the test
function of `Q_t Π_x ΨXᵢ (x)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weighted kernel `y ↦ Q_t(x, y) (y_i - x_i) / t^(1/4)`. -/
def semigroupCoordKernel (t : ℝ) (x : ParabolicSpace) (i : Fin 3) (y : ParabolicSpace) : ℝ :=
  parabolicSemigroup.kernel t x y * (y.2 i - x.2 i) / t ^ (1 / 4 : ℝ)

/-- The periodisation of `y ↦ Q_t(x, y) (y_i - x_i) / t^(1/4)`. -/
def semigroupPeriodisedCoord (t : ℝ) (x : ParabolicSpace) (i : Fin 3) (u : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, semigroupCoordKernel t x i (u.1, torusRep u.2 + fun j => (k j : ℝ))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem abs_coord_le_parabolicNorm (z : ParabolicSpace) (i : Fin 3) :
    |z.2 i| ≤ parabolicNorm z := by
  unfold parabolicNorm
  have := Finset.single_le_sum (f := fun j => |z.2 j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  have := Real.sqrt_nonneg |z.1|
  linarith

theorem measurable_coordKernel (t : ℝ) (x : ParabolicSpace) (i : Fin 3) :
    Measurable (semigroupCoordKernel t x i) := by
  unfold semigroupCoordKernel
  exact ((measurable_parabolicSemigroup_kernel t x).mul
    (((measurable_pi_apply i).comp measurable_snd).sub measurable_const)).div_const _

/-- **The coordinate-weighted periodised semigroup kernel is a test profile.** -/
theorem exists_semigroupTestProfile_semigroupPeriodisedCoord (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupTestProfile (Phi43.spaceTimeProj x) (t ^ (1 / 4 : ℝ)) B
        (fun r => parabolicMomentConst (r + 1)) (semigroupPeriodisedCoord t x i) := by
  obtain ⟨Cw, hCw0, hCw⟩ := exists_abs_parabolicKernel_mul_norm_le 1
  obtain ⟨L, hL0, hL⟩ := tsum_abs_periodise_le
  refine ⟨Cw * L, mul_nonneg hCw0 hL0, fun {t} ht ht1 x => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hdec : ∀ y : ParabolicSpace, |semigroupCoordKernel t x i y| ≤
      (Cw * t ^ (-(5 / 4 : ℝ))) * ∏ j : Fin 3, ((1 + |x.2 j - y.2 j|) ^ 2)⁻¹ := by
    intro y
    unfold semigroupCoordKernel
    have h1 := hCw ht ht1 (x - y)
    rw [pow_one] at h1
    have hn : |y.2 i - x.2 i| ≤ parabolicNorm (x - y) := by
      rw [abs_sub_comm]; exact abs_coord_le_parabolicNorm (x - y) i
    calc |parabolicSemigroup.kernel t x y * (y.2 i - x.2 i) / t ^ (1 / 4 : ℝ)|
        = |parabolicSemigroup.kernel t x y| * |y.2 i - x.2 i| / t ^ (1 / 4 : ℝ) := by
          rw [abs_div, abs_mul, abs_of_pos hlam]
      _ ≤ |parabolicKernel t (x - y)| * (parabolicNorm (x - y) / t ^ (1 / 4 : ℝ)) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hlam.le) (abs_nonneg _)
      _ ≤ _ := h1
  have hsup : ∀ u : SpaceTime,
      Summable (fun k : Fin 3 → ℤ =>
        |semigroupCoordKernel t x i (u.1, torusRep u.2 + fun j => (k j : ℝ))|) ∧
      ∑' k : Fin 3 → ℤ, |semigroupCoordKernel t x i (u.1, torusRep u.2 + fun j => (k j : ℝ))| ≤
        (Cw * L) * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ := by
    intro u
    obtain ⟨hs, hb⟩ := hL (h := semigroupCoordKernel t x i)
      (C := Cw * t ^ (-(5 / 4 : ℝ))) (a0 := x.2)
      (mul_nonneg hCw0 (Real.rpow_nonneg ht.le _)) hdec u
    refine ⟨hs, hb.trans (le_of_eq ?_)⟩
    rw [rpow_quarter_pow_five_inv ht]
    ring
  have hdi : ∀ r : ℝ, 0 ≤ r → ∀ y : ParabolicSpace,
      |semigroupCoordKernel t x i y| * parabolicNorm (y - x) ^ r ≤
        (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
          t ^ (1 / 4 : ℝ) := by
    intro r hr y
    unfold semigroupCoordKernel
    have hn : |y.2 i - x.2 i| ≤ parabolicNorm (y - x) := abs_coord_le_parabolicNorm (y - x) i
    have hp : 0 ≤ parabolicNorm (y - x) ^ r := Real.rpow_nonneg (parabolicNorm_nonneg _) _
    rw [abs_div, abs_of_pos hlam, abs_mul, Real.rpow_add' (parabolicNorm_nonneg _) (by linarith),
      Real.rpow_one]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlam]
    calc |parabolicSemigroup.kernel t x y| * |y.2 i - x.2 i| * parabolicNorm (y - x) ^ r
        ≤ |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) * parabolicNorm (y - x) ^ r := by
          gcongr
      _ = _ := by ring
  refine semigroupTestProfile_periodise (measurable_coordKernel t x i) hsup ?_ ?_
  · intro r hr
    have hI := (parabolicSemigroup.integrable_moment ht (r := r + 1) (by linarith) x).div_const
      (t ^ (1 / 4 : ℝ))
    refine hI.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp (measurable_coordKernel t x i)).mul
        ((continuous_parabolicNorm.measurable.comp
          (measurable_id.sub measurable_const)).pow_const r)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _))]
      exact hdi r hr y
  · intro r hr
    have hI := (parabolicSemigroup.integrable_moment ht (r := r + 1) (by linarith) x).div_const
      (t ^ (1 / 4 : ℝ))
    have hi2 : Integrable (fun y => |semigroupCoordKernel t x i y| * parabolicNorm (y - x) ^ r) := by
      refine hI.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact ((continuous_abs.measurable.comp (measurable_coordKernel t x i)).mul
          ((continuous_parabolicNorm.measurable.comp
            (measurable_id.sub measurable_const)).pow_const r)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
          (Real.rpow_nonneg (parabolicNorm_nonneg _) _))]
        exact hdi r hr y
    calc ∫ y, |semigroupCoordKernel t x i y| * parabolicNorm (y - x) ^ r
        ≤ ∫ y, (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
            t ^ (1 / 4 : ℝ) := integral_mono hi2 hI (hdi r hr)
      _ = (∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
            t ^ (1 / 4 : ℝ) := integral_div _ _
      _ ≤ (parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4)) / t ^ (1 / 4 : ℝ) := by
          gcongr
          have := parabolicSemigroup.moment_le ht (r := r + 1) (by linarith) x
          exact this
      _ = parabolicMomentConst (r + 1) * (t ^ (1 / 4 : ℝ)) ^ r := by
          rw [rpow_quarter_rpow ht, mul_div_assoc, ← Real.rpow_sub ht]
          congr 2
          ring

end RegularityStructures

end
