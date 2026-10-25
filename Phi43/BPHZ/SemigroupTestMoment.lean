/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestPeriodise
public import RegularityStructures.Torus.KernelBoundsBasic
public import Phi43.BPHZ.ChaosReductionIntegralSupport
public import RegularityStructures.Analysis.Kernel.Moments

/-!
# Moments of the periodised semigroup kernel

For `t > 0`, `r ≥ 0` and the periodised kernel `q^♯_t(x, ·)` on `ℝ × T³`,
`∫ |q^♯_t(x, u)| s(u - proj x)^r du ≤ M_r t^(r/4)`
(`integral_abs_semigroupPeriodised_mul_le`), with `M_r = parabolicMomentConst r` the moment
constant of `parabolicSemigroup`.  The torus size is dominated by the parabolic size of any lift,
`s(proj d) ≤ ‖d‖_𝔰` (`torusParabolicSize_spaceTimeProj_le`), so the `[0, ∞]`-valued unfolding turns
the periodised moment into the moment of `Q_t(x, ·)` on `ℝ⁴`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- The torus size of a projected displacement is at most its parabolic size. -/
theorem torusParabolicSize_spaceTimeProj_le (d : ParabolicSpace) :
    torusParabolicSize (Phi43.spaceTimeProj d) ≤ parabolicNorm d := by
  have hc : ∀ i, |torusCenteredRep (torusProj d.2) i| ≤ |d.2 i| := fun i =>
    abs_torusCenteredRep_le_abs_of_torusProj rfl i
  have hsp : torusSpatialNorm (torusProj d.2) ≤ ∑ i, |d.2 i| := by
    unfold torusSpatialNorm
    rw [Real.sqrt_le_iff]
    refine ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
    unfold sqNorm3
    have h2 : ∀ i, torusCenteredRep (torusProj d.2) i ^ 2 ≤ |d.2 i| ^ 2 := fun i => by
      rw [← sq_abs (torusCenteredRep (torusProj d.2) i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
    calc ∑ i, torusCenteredRep (torusProj d.2) i ^ 2 ≤ ∑ i, |d.2 i| ^ 2 :=
          Finset.sum_le_sum fun i _ => h2 i
      _ ≤ (∑ i, |d.2 i|) ^ 2 := by
          simp only [Fin.sum_univ_three]
          nlinarith [abs_nonneg (d.2 0), abs_nonneg (d.2 1), abs_nonneg (d.2 2),
            mul_nonneg (abs_nonneg (d.2 0)) (abs_nonneg (d.2 1)),
            mul_nonneg (abs_nonneg (d.2 0)) (abs_nonneg (d.2 2)),
            mul_nonneg (abs_nonneg (d.2 1)) (abs_nonneg (d.2 2))]
  unfold torusParabolicSize parabolicNorm
  exact add_le_add le_rfl hsp

/-- **Moment bound for the periodised semigroup kernel.** -/
theorem integral_abs_semigroupPeriodised_mul_le {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r)
    (x : ParabolicSpace) :
    Integrable (fun u : SpaceTime => |semigroupPeriodised t x u| *
        torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) ∧
      ∫ u : SpaceTime, |semigroupPeriodised t x u| *
        torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤
          parabolicMomentConst r * t ^ (r / 4) := by
  set Θ : ParabolicSpace → ℝ := fun y =>
    |parabolicSemigroup.kernel t x y| * parabolicSemigroup.scaleDist y x ^ r with hΘ
  have hΘi : Integrable Θ := parabolicSemigroup.integrable_moment ht hr x
  have hΘ0 : ∀ y, 0 ≤ Θ y := fun y => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  have hΘm : Measurable Θ :=
    (continuous_abs.measurable.comp (measurable_parabolicSemigroup_kernel t x)).mul
      ((continuous_parabolicNorm.measurable.comp (measurable_id.sub measurable_const)).pow_const _)
  -- the pointwise `[0, ∞]` bound
  set f : SpaceTime → ℝ := fun u => |semigroupPeriodised t x u| *
    torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r with hf
  have hf0 : ∀ u, 0 ≤ f u := fun u => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hfm : Measurable f :=
    (continuous_abs.measurable.comp (measurable_semigroupPeriodised t x)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _)
  have hpt : ∀ u : SpaceTime, ENNReal.ofReal (f u) ≤ ∑' k : Fin 3 → ℤ,
      ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun i => (k i : ℝ))) := by
    intro u
    have hsize : ∀ k : Fin 3 → ℤ, torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤
        parabolicNorm ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x) ^ r := by
      intro k
      refine Real.rpow_le_rpow (torusParabolicSize_nonneg _) ?_ hr
      have h := torusParabolicSize_spaceTimeProj_le ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x)
      rwa [Phi43.spaceTimeProj_sub, spaceTimeProj_semigroup_lift] at h
    calc ENNReal.ofReal (f u)
        = ‖semigroupPeriodised t x u‖ₑ *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) := by
          rw [hf, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
      _ ≤ (∑' k : Fin 3 → ℤ, ‖parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ) *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) :=
          by gcongr; exact enorm_tsum_le_tsum_enorm
      _ = ∑' k : Fin 3 → ℤ, ‖parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) :=
          ENNReal.tsum_mul_right.symm
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [Real.enorm_eq_ofReal_abs]
          show _ ≤ ENNReal.ofReal (|parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun i => (k i : ℝ))| *
              parabolicNorm ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x) ^ r)
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hsize k))
  have hlint : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) ≤ ENNReal.ofReal (∫ y, Θ y) := by
    calc ∫⁻ u : SpaceTime, ENNReal.ofReal (f u)
        ≤ ∫⁻ u : SpaceTime, ∑' k : Fin 3 → ℤ,
            ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun i => (k i : ℝ))) :=
          lintegral_mono hpt
      _ = ∫⁻ y : ParabolicSpace, ENNReal.ofReal (Θ y) :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum
            (H := fun y => ENNReal.ofReal (Θ y)) hΘm.ennreal_ofReal).symm
      _ = ENNReal.ofReal (∫ y, Θ y) :=
          (ofReal_integral_eq_lintegral_ofReal hΘi (Filter.Eventually.of_forall hΘ0)).symm
  have hbd : 0 ≤ parabolicMomentConst r * t ^ (r / 4) :=
    mul_nonneg (parabolicMomentConst_nonneg r) (Real.rpow_nonneg ht.le _)
  have hmom : ∫ y, Θ y ≤ parabolicMomentConst r * t ^ (r / 4) :=
    parabolicSemigroup.moment_le ht hr x
  have hlt : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) < ⊤ :=
    lt_of_le_of_lt (hlint.trans (ENNReal.ofReal_le_ofReal hmom)) ENNReal.ofReal_lt_top
  have hfi : Integrable f :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hf0)).2 hlt⟩
  refine ⟨hfi, ?_⟩
  have h1 : ENNReal.ofReal (∫ u, f u) ≤ ENNReal.ofReal (parabolicMomentConst r * t ^ (r / 4)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
    exact hlint.trans (ENNReal.ofReal_le_ofReal hmom)
  exact (ENNReal.ofReal_le_ofReal_iff hbd).1 h1

end RegularityStructures

end
