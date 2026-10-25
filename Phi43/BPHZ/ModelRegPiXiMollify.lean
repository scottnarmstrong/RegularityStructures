/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiXiTranslate
public import Phi43.BPHZ.ModelRegPiXiScale
public import Phi43.BPHZ.NoiseTreeMollifyDiff
public import Phi43.BPHZ.NoiseTreeUnfold
public import Phi43.BPHZ.NoiseTreeYoung
public import Phi43.Stochastic.ConstantsComparisonPeriodise
public import Phi43.BPHZ.SemigroupTestKernel

/-!
# Distance of the smeared periodised semigroup kernel to the kernel

For `a ∈ [0, 1]`, `ε, t ∈ (0, 1]`, `lam = t^(1/4)` and `ψ = q^♯_t(x, ·)`,

`∫ (ψ ⋆ ρ_ε^♯ - ψ)² ≤ C ε^a lam^(-(5 + a))`

(`noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le`), with `C` depending only on `ρ` and
`a`.  The `L¹` translation modulus of `ψ` (`ModelRegPiXiTranslate`) is combined with the sup bound
by `‖f‖₂² ≤ ‖f‖_∞ ‖f‖₁`, and with the trivial bound `2‖ψ‖₁` for large shifts, giving
`∫ (ψ(· + proj y) - ψ)² ≲ lam^(-5) (lam⁻¹ ‖y‖)^a`; then the unfolding of the periodised mollifier
and its fractional parabolic moment `ε^a`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem le_max_mul_rpow {f K₁ K₂ r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hK₁ : 0 ≤ K₁) (h₁ : r ≤ 1 → f ≤ K₁ * r) (h₂ : 1 < r → f ≤ K₂) :
    f ≤ max K₁ K₂ * r ^ a := by
  rcases le_or_gt r 1 with h | h
  · have hra : r ≤ r ^ a := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' hr h ha0 ha1
    exact (h₁ h).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hr).trans
      (mul_le_mul_of_nonneg_left hra ((hK₁.trans (le_max_left _ _)))))
  · have hra : 1 ≤ r ^ a := Real.one_le_rpow h.le ha0
    exact (h₂ h).trans (by
      calc K₂ ≤ max K₁ K₂ := le_max_right _ _
        _ = max K₁ K₂ * 1 := (mul_one _).symm
        _ ≤ max K₁ K₂ * r ^ a := mul_le_mul_of_nonneg_left hra (hK₁.trans (le_max_left _ _)))

/-- **`L¹` translation modulus of `q^♯_t(x, ·)`, Hölder form.** -/
theorem exists_integral_abs_semigroupPeriodised_add_sub_le_rpow {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x y : ParabolicSpace),
      ∫ u : SpaceTime, |semigroupPeriodised t x (u + spaceTimeProj y) -
          semigroupPeriodised t x u| ≤ K * ((t ^ (1 / 4 : ℝ))⁻¹ * parabolicNorm y) ^ a := by
  obtain ⟨K₁, hK₁, hK₁'⟩ := exists_integral_abs_semigroupPeriodised_add_sub_le
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  have hM0 : 0 ≤ parabolicMomentConst 0 := (hB (t := 1) one_pos le_rfl 0).mom_zero_nonneg
  refine ⟨max K₁ (2 * parabolicMomentConst 0), le_max_of_le_left hK₁, fun {t} ht ht1 x y => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hinv : t ^ (-(1 / 4 : ℝ)) = (t ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg ht.le _
  refine le_max_mul_rpow (mul_nonneg (inv_nonneg.2 hlam.le) (parabolicNorm_nonneg y)) ha0 ha1 hK₁
    (fun hr => ?_) (fun hr => ?_)
  · have hy : parabolicNorm y ≤ t ^ (1 / 4 : ℝ) := by
      rw [inv_mul_le_iff₀ hlam] at hr
      linarith
    have := hK₁' ht ht1 x y hy
    rwa [hinv] at this
  · set ψ := semigroupPeriodised t x with hψ
    have h := hB ht ht1 x
    have hs : Integrable (fun u => ψ (u + spaceTimeProj y)) := h.integrable.comp_add_right _
    calc ∫ u : SpaceTime, |ψ (u + spaceTimeProj y) - ψ u|
        ≤ ∫ u : SpaceTime, (|ψ (u + spaceTimeProj y)| + |ψ u|) :=
          integral_mono ((hs.sub h.integrable).abs) (hs.abs.add h.integrable_abs)
            (fun u => abs_sub _ _)
      _ = 2 * ∫ u, |ψ u| := by
          rw [integral_add hs.abs h.integrable_abs,
            integral_add_right_eq_self (μ := volume) (fun u => |ψ u|) (spaceTimeProj y)]
          ring
      _ ≤ 2 * parabolicMomentConst 0 := by
          have := h.integral_abs_le
          linarith

end RegularityStructures.Phi43

end
