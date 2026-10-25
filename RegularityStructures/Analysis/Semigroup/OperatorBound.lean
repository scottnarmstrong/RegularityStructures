/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Bounds for the semigroup operators

Integrability and the bound `|Q_t g| ≤ M₀ ‖g‖_∞`, the semigroup identity on bounded functions
(`apply_apply`), and uniqueness: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C t^β`, `β > 0`,
coincide (`eq_of_abs_sub_le`).

Source: [Hos25, proof of Theorem 4.1].
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem integrable_kernel_mul_of_bound {t : ℝ} (ht : 0 < t) (x : E) {g : E → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    Integrable (fun y => K.kernel t x y * g y) μ :=
  (K.integrable_kernel ht x).mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa using hB y)

theorem integral_abs_kernel_mul_le {t : ℝ} (ht : 0 < t) (x : E) {g : E → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) : ∫ y, |K.kernel t x y * g y| ∂μ ≤ K.momentConst 0 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  calc ∫ y, |K.kernel t x y * g y| ∂μ ≤ ∫ y, |K.kernel t x y| * B ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
          ((K.integrable_kernel ht x).abs.mul_const B) (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)
    _ = (∫ y, |K.kernel t x y| ∂μ) * B := integral_mul_const _ _
    _ ≤ K.momentConst 0 * B := mul_le_mul_of_nonneg_right (K.integral_abs_kernel_le ht x) hB0

/-- The bound `|Q_t g| ≤ M₀ ‖g‖_∞`, without measurability of `g`. -/
theorem abs_apply_le_of_bound {t : ℝ} (ht : 0 < t) {g : E → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (x : E) : |K.apply t g x| ≤ K.momentConst 0 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  have h := norm_integral_le_of_norm_le ((K.integrable_kernel ht x).abs.mul_const B)
    (f := fun y => K.kernel t x y * g y) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _))
  rw [integral_mul_const] at h
  calc |K.apply t g x| ≤ (∫ y, |K.kernel t x y| ∂μ) * B := by simpa [apply] using h
    _ ≤ K.momentConst 0 * B := mul_le_mul_of_nonneg_right (K.integral_abs_kernel_le ht x) hB0

theorem apply_apply [SFinite μ] {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {g : E → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) (x : E) :
    K.apply s (K.apply t g) x = K.apply (s + t) g x := by
  have hmeas : Measurable (fun p : E × E => K.kernel s x p.1 * (K.kernel t p.1 p.2 * g p.2)) :=
    ((K.measurable_kernel_right s x).comp measurable_fst).mul
      ((K.measurable_kernel t).mul (hg.comp measurable_snd))
  have hint : Integrable (fun p : E × E =>
      K.kernel s x p.1 * (K.kernel t p.1 p.2 * g p.2)) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · dsimp only
      exact (K.integrable_kernel_mul_of_bound ht y hg hB).const_mul _
    · refine Integrable.mono' ((K.integrable_kernel hs x).abs.mul_const (K.momentConst 0 * B))
        hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      have e : ∫ z, ‖K.kernel s x y * (K.kernel t y z * g z)‖ ∂μ =
          |K.kernel s x y| * ∫ z, |K.kernel t y z * g z| ∂μ := by
        rw [← integral_const_mul]
        simp only [Real.norm_eq_abs, abs_mul]
      have hnn : 0 ≤ ∫ z, ‖K.kernel s x y * (K.kernel t y z * g z)‖ ∂μ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, e]
      exact mul_le_mul_of_nonneg_left (K.integral_abs_kernel_mul_le ht y hB) (abs_nonneg _)
  calc K.apply s (K.apply t g) x
      = ∫ y, ∫ z, K.kernel s x y * (K.kernel t y z * g z) ∂μ ∂μ := by
        simp only [apply, ← integral_const_mul]
    _ = ∫ z, ∫ y, K.kernel s x y * (K.kernel t y z * g z) ∂μ ∂μ :=
        integral_integral_swap (f := fun y z => K.kernel s x y * (K.kernel t y z * g z)) hint
    _ = ∫ z, K.kernel (s + t) x z * g z ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [← K.semigroup hs ht x z, ← integral_mul_const]
        simp only [mul_assoc]
    _ = K.apply (s + t) g x := rfl

/-- Uniqueness: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C t^β` for `0 < t ≤ 1` (`β > 0`)
coincide ([Hos25, proof of Theorem 4.1]). -/
theorem eq_of_abs_sub_le {Λ Λ' : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛ' : Λ' ∈ K.distributions) {β C : ℝ} (hβ : 0 < β)
    (h : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x, |Λ t x - Λ' t x| ≤ C * t ^ β) : Λ = Λ' := by
  have hD : Λ - Λ' ∈ K.distributions := K.distributions.sub_mem hΛ hΛ'
  have hD' : ∀ t x, (Λ - Λ') t x = Λ t x - Λ' t x := fun _ _ => rfl
  have hshift : ∀ {s t : ℝ}, 0 < s → s < t → ∀ x,
      (Λ - Λ') t x = K.apply (t - s) ((Λ - Λ') s) x := by
    intro s t hs hst x
    rw [K.apply_eq hD (sub_pos.2 hst) hs]
    simp
  have hzero : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x, (Λ - Λ') t x = 0 := by
    intro t ht x
    have hle : ∀ s ∈ Set.Ioo (0 : ℝ) t, |(Λ - Λ') t x| ≤ K.momentConst 0 * (C * s ^ β) := by
      intro s hs
      rw [hshift hs.1 hs.2 x]
      exact K.abs_apply_le_of_bound (sub_pos.2 hs.2) (fun y => by
        rw [hD']; exact h s ⟨hs.1, hs.2.le.trans ht.2⟩ y) x
    have h0 : Tendsto (fun s : ℝ => K.momentConst 0 * (C * s ^ β)) (𝓝[>] 0) (𝓝 0) := by
      have := (((Real.continuous_rpow_const hβ.le).const_mul C).const_mul
        (K.momentConst 0)).tendsto 0
      rw [Real.zero_rpow hβ.ne', mul_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto h0 (Filter.mem_of_superset (Ioo_mem_nhdsGT ht.1) hle)
    exact abs_nonpos_iff.1 (this.trans le_rfl)
  funext t
  rcases le_or_gt t 0 with ht | ht
  · rw [K.eq_zero_of_nonpos hΛ ht, K.eq_zero_of_nonpos hΛ' ht]
  rcases le_or_gt t 1 with ht1 | ht1
  · funext x
    have := hzero t ⟨ht, ht1⟩ x
    simpa [sub_eq_zero] using this
  · funext x
    have h1 : (Λ - Λ') 1 = 0 := funext fun y => hzero 1 ⟨one_pos, le_rfl⟩ y
    have := hshift one_pos ht1 x
    rw [h1] at this
    simp only [apply, Pi.zero_apply, mul_zero, integral_zero] at this
    simpa [sub_eq_zero] using this

end RegularityStructures.RegularisingSemigroup

end
