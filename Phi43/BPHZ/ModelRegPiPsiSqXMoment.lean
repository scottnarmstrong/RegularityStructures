/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXKernel
public import Phi43.BPHZ.SemigroupTestKernel

/-!
# The coordinate-weighted periodised kernel is a rescaled test profile

For `t ∈ (0, 1]` and `lam = t^(1/4)`, the function `u ↦ lam⁻¹ g_i(u)` with
`g_i = semigroupPeriodisedX t x i` is a `SemigroupTestProfile` at the base point `proj x` and scale
`lam`, with the sup constant of `exists_abs_semigroupPeriodisedX_le` and moment constants
`r ↦ parabolicMomentConst (r + 1)`.  The moment bound
`∫ |g_i| s(· - proj x)^r ≤ M_{r+1} t^((r+1)/4)` follows from the unfolding of the `ℝ⁴` moment of
`Q_t(x, ·)`, since `|yᵢ - xᵢ| ≤ ‖y - x‖`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem measurable_semigroupPeriodisedX (t : ℝ) (x : ParabolicSpace) (i : Fin 3) :
    Measurable (semigroupPeriodisedX t x i) := by
  unfold semigroupPeriodisedX
  refine Measurable.tsum fun k => ?_
  have h1 : Measurable (fun u : SpaceTime =>
      parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ))) :=
    (measurable_parabolicSemigroup_kernel t x).comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
  have h2 : Measurable (fun u : SpaceTime => (torusRep u.2 i + (k i : ℝ)) - x.2 i) :=
    (((measurable_pi_apply i).comp (measurable_torusRep.comp measurable_snd)).add_const _).sub_const _
  exact h1.mul h2

theorem abs_coord_le_parabolicNorm (z : ParabolicSpace) (i : Fin 3) :
    |z.2 i| ≤ parabolicNorm z := by
  unfold parabolicNorm
  have h : |z.2 i| ≤ ∑ j, |z.2 j| :=
    Finset.single_le_sum (f := fun j => |z.2 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith [Real.sqrt_nonneg |z.1|]

/-- **Moment bound for the coordinate-weighted periodised semigroup kernel.** -/
theorem integral_abs_semigroupPeriodisedX_mul_le {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r)
    (x : ParabolicSpace) (i : Fin 3) :
    Integrable (fun u : SpaceTime => |semigroupPeriodisedX t x i u| *
        torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) ∧
      ∫ u : SpaceTime, |semigroupPeriodisedX t x i u| *
        torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤
          parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4) := by
  have hr1 : 0 ≤ r + 1 := by linarith
  set Θ : ParabolicSpace → ℝ := fun y =>
    |parabolicSemigroup.kernel t x y| * parabolicSemigroup.scaleDist y x ^ (r + 1) with hΘ
  have hΘi : Integrable Θ := parabolicSemigroup.integrable_moment ht hr1 x
  have hΘ0 : ∀ y, 0 ≤ Θ y := fun y => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  have hΘm : Measurable Θ :=
    (continuous_abs.measurable.comp (measurable_parabolicSemigroup_kernel t x)).mul
      ((continuous_parabolicNorm.measurable.comp (measurable_id.sub measurable_const)).pow_const _)
  set f : SpaceTime → ℝ := fun u => |semigroupPeriodisedX t x i u| *
    torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r with hf
  have hf0 : ∀ u, 0 ≤ f u := fun u => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hfm : Measurable f :=
    (continuous_abs.measurable.comp (measurable_semigroupPeriodisedX t x i)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _)
  have hpt : ∀ u : SpaceTime, ENNReal.ofReal (f u) ≤ ∑' k : Fin 3 → ℤ,
      ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun j => (k j : ℝ))) := by
    intro u
    have hsize : ∀ k : Fin 3 → ℤ, torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤
        parabolicNorm ((u.1, torusRep u.2 + fun j => (k j : ℝ)) - x) ^ r := by
      intro k
      refine Real.rpow_le_rpow (torusParabolicSize_nonneg _) ?_ hr
      have h := torusParabolicSize_spaceTimeProj_le ((u.1, torusRep u.2 + fun j => (k j : ℝ)) - x)
      rwa [Phi43.spaceTimeProj_sub, spaceTimeProj_semigroup_lift] at h
    calc ENNReal.ofReal (f u)
        = ‖semigroupPeriodisedX t x i u‖ₑ *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) := by
          rw [hf, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
      _ ≤ (∑' k : Fin 3 → ℤ, ‖parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun j => (k j : ℝ)) *
              ((torusRep u.2 i + (k i : ℝ)) - x.2 i)‖ₑ) *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) :=
          by gcongr; exact enorm_tsum_le_tsum_enorm
      _ = ∑' k : Fin 3 → ℤ, ‖parabolicSemigroup.kernel t x
            (u.1, torusRep u.2 + fun j => (k j : ℝ)) *
              ((torusRep u.2 i + (k i : ℝ)) - x.2 i)‖ₑ *
            ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) :=
          ENNReal.tsum_mul_right.symm
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          set y : ParabolicSpace := (u.1, torusRep u.2 + fun j => (k j : ℝ)) with hy
          have hw : |(torusRep u.2 i + (k i : ℝ)) - x.2 i| ≤ parabolicNorm (y - x) := by
            have := abs_coord_le_parabolicNorm (y - x) i
            simpa [hy] using this
          have hN := parabolicNorm_nonneg (y - x)
          have hmain : |parabolicSemigroup.kernel t x y| *
              |(torusRep u.2 i + (k i : ℝ)) - x.2 i| *
              torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤ Θ y := by
            have hexp : parabolicNorm (y - x) ^ (r + 1) = parabolicNorm (y - x) ^ r *
                parabolicNorm (y - x) := by
              rw [Real.rpow_add_of_nonneg hN hr zero_le_one, Real.rpow_one]
            have hΘy : Θ y = |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1) :=
              rfl
            rw [hΘy, hexp]
            calc |parabolicSemigroup.kernel t x y| * |(torusRep u.2 i + (k i : ℝ)) - x.2 i| *
                  torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r
                ≤ |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) *
                    parabolicNorm (y - x) ^ r := by
                  exact mul_le_mul (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (hsize k)
                    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) (by positivity)
              _ = _ := by ring
          rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hmain
  have hlint : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) ≤ ENNReal.ofReal (∫ y, Θ y) := by
    calc ∫⁻ u : SpaceTime, ENNReal.ofReal (f u)
        ≤ ∫⁻ u : SpaceTime, ∑' k : Fin 3 → ℤ,
            ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun j => (k j : ℝ))) :=
          lintegral_mono hpt
      _ = ∫⁻ y : ParabolicSpace, ENNReal.ofReal (Θ y) :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum
            (H := fun y => ENNReal.ofReal (Θ y)) hΘm.ennreal_ofReal).symm
      _ = ENNReal.ofReal (∫ y, Θ y) :=
          (ofReal_integral_eq_lintegral_ofReal hΘi (Filter.Eventually.of_forall hΘ0)).symm
  have hbd : 0 ≤ parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4) :=
    mul_nonneg (parabolicMomentConst_nonneg _) (Real.rpow_nonneg ht.le _)
  have hmom : ∫ y, Θ y ≤ parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4) :=
    parabolicSemigroup.moment_le ht hr1 x
  have hlt : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) < ⊤ :=
    lt_of_le_of_lt (hlint.trans (ENNReal.ofReal_le_ofReal hmom)) ENNReal.ofReal_lt_top
  have hfi : Integrable f :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hf0)).2 hlt⟩
  refine ⟨hfi, ?_⟩
  have h1 : ENNReal.ofReal (∫ u, f u) ≤
      ENNReal.ofReal (parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
    exact hlint.trans (ENNReal.ofReal_le_ofReal hmom)
  exact (ENNReal.ofReal_le_ofReal_iff hbd).1 h1

/-- **The rescaled coordinate-weighted periodised kernel is a test profile.** -/
theorem exists_semigroupTestProfile_semigroupPeriodisedX (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupTestProfile (Phi43.spaceTimeProj x) (t ^ (1 / 4 : ℝ)) B
        (fun r => parabolicMomentConst (r + 1))
        (fun u => (t ^ (1 / 4 : ℝ))⁻¹ * semigroupPeriodisedX t x i u) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_semigroupPeriodisedX_le i
  refine ⟨B, hB0, fun {t} ht ht1 x => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  refine ⟨measurable_const.mul (measurable_semigroupPeriodisedX t x i), fun u => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · rw [abs_mul, abs_of_pos (inv_pos.2 hlam)]
    calc (t ^ (1 / 4 : ℝ))⁻¹ * |semigroupPeriodisedX t x i u|
        ≤ (t ^ (1 / 4 : ℝ))⁻¹ * (B * (t ^ (1 / 4 : ℝ) * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹)) :=
          mul_le_mul_of_nonneg_left (hB ht ht1 x u) (inv_nonneg.2 hlam.le)
      _ = B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ := by field_simp
  · have h := (integral_abs_semigroupPeriodisedX_mul_le ht hr x i).1
    refine (h.const_mul (t ^ (1 / 4 : ℝ))⁻¹).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [abs_mul, abs_of_pos (inv_pos.2 hlam)]
    ring
  · have h := integral_abs_semigroupPeriodisedX_mul_le ht hr x i
    have e : ∫ u : SpaceTime, |(t ^ (1 / 4 : ℝ))⁻¹ * semigroupPeriodisedX t x i u| *
        torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r =
        (t ^ (1 / 4 : ℝ))⁻¹ * ∫ u : SpaceTime, |semigroupPeriodisedX t x i u| *
          torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [abs_mul, abs_of_pos (inv_pos.2 hlam)]
      ring
    rw [e]
    have hp : (t ^ (1 / 4 : ℝ)) ^ r = (t ^ (1 / 4 : ℝ))⁻¹ * t ^ ((r + 1) / 4) := by
      rw [rpow_quarter_rpow ht, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
      congr 1
      ring
    rw [hp, ← mul_assoc, mul_comm (parabolicMomentConst (r + 1)), mul_assoc]
    exact mul_le_mul_of_nonneg_left h.2 (inv_nonneg.2 hlam.le)

end RegularityStructures

end
