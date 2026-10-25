/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Defs
public import RegularityStructures.Analysis.Semigroup.Operator

/-!
# The operators `Q_t` on functions of growth `ρ`

For a moderate weight `ρ` and `|g| ≤ B ρ`:

* `integrable_abs_kernel_mul_weight`, `integral_abs_kernel_mul_weight_le`:
  `∫ |Q_t(x, y)| ρ(y) dy ≤ ρ(x) 2^p (M₀ + M_p t^{p/ℓ})`;
* `abs_apply_le_of_weight_bound`: `|Q_t g (x)| ≤ B ρ(x) · weightConst p t`;
* `apply_apply_of_weight_bound`: `Q_s Q_t g = Q_{s+t} g`;
* `eq_of_abs_sub_le_weight`: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C ρ t^β` coincide.

Source: [Hos25] = arXiv:2310.07396v2, proof of Theorem 4.1, with weights.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  {ρ : E → ℝ} {p : ℝ}

/-- The dominating function `ρ(x) 2^p (|Q| + |Q| d^p)` of `|Q_t(x, ·)| ρ`. -/
private theorem integrable_dom {t : ℝ} (ht : 0 < t) (hp : 0 ≤ p) (x : E) (c : ℝ) :
    Integrable (fun y => c * ((2 : ℝ) ^ p *
      (|K.kernel t x y| + |K.kernel t x y| * K.scaleDist y x ^ p))) μ :=
  (((K.integrable_kernel ht x).abs.add (K.integrable_moment ht hp x)).const_mul _).const_mul _

theorem integrable_abs_kernel_mul_weight (hρ : K.IsModerateWeight ρ p) {t : ℝ} (ht : 0 < t)
    (x : E) : Integrable (fun y => |K.kernel t x y| * ρ y) μ := by
  refine Integrable.mono' (K.integrable_dom ht hρ.nonneg_exp x (ρ x))
    ((continuous_abs.measurable.comp (K.measurable_kernel_right t x)).mul hρ.measurable).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hρ.pos y).le)]
  calc |K.kernel t x y| * ρ y
      ≤ |K.kernel t x y| * (ρ x * ((2 : ℝ) ^ p * (1 + K.scaleDist y x ^ p))) :=
        mul_le_mul_of_nonneg_left (hρ.le_mul x y) (abs_nonneg _)
    _ = _ := by ring

theorem integral_abs_kernel_mul_weight_le (hρ : K.IsModerateWeight ρ p) {t : ℝ} (ht : 0 < t)
    (x : E) : ∫ y, |K.kernel t x y| * ρ y ∂μ ≤ ρ x * K.weightConst p t := by
  have hp := hρ.nonneg_exp
  calc ∫ y, |K.kernel t x y| * ρ y ∂μ
      ≤ ∫ y, ρ x * ((2 : ℝ) ^ p *
          (|K.kernel t x y| + |K.kernel t x y| * K.scaleDist y x ^ p)) ∂μ := by
        refine integral_mono (K.integrable_abs_kernel_mul_weight hρ ht x)
          (K.integrable_dom ht hp x (ρ x)) fun y => ?_
        calc |K.kernel t x y| * ρ y
            ≤ |K.kernel t x y| * (ρ x * ((2 : ℝ) ^ p * (1 + K.scaleDist y x ^ p))) :=
              mul_le_mul_of_nonneg_left (hρ.le_mul x y) (abs_nonneg _)
          _ = _ := by ring
    _ = ρ x * ((2 : ℝ) ^ p * ((∫ y, |K.kernel t x y| ∂μ) +
          ∫ y, |K.kernel t x y| * K.scaleDist y x ^ p ∂μ)) := by
        rw [integral_const_mul, integral_const_mul,
          integral_add (K.integrable_kernel ht x).abs (K.integrable_moment ht hp x)]
    _ ≤ ρ x * K.weightConst p t := by
        refine mul_le_mul_of_nonneg_left ?_ (hρ.pos x).le
        unfold weightConst
        refine mul_le_mul_of_nonneg_left (add_le_add (K.integral_abs_kernel_le ht x)
          (K.moment_le ht hp x)) (Real.rpow_nonneg (by norm_num) _)

theorem integral_abs_kernel_mul_le_of_weight_bound (hρ : K.IsModerateWeight ρ p) {t : ℝ}
    (ht : 0 < t) (x : E) {g : E → ℝ} {B : ℝ} (hB : ∀ y, |g y| ≤ B * ρ y) :
    ∫ y, |K.kernel t x y * g y| ∂μ ≤ B * ρ x * K.weightConst p t := by
  have hB0 : 0 ≤ B := by
    by_contra h
    have := hB x
    have := mul_neg_of_neg_of_pos (not_le.1 h) (hρ.pos x)
    linarith [abs_nonneg (g x)]
  calc ∫ y, |K.kernel t x y * g y| ∂μ ≤ ∫ y, B * (|K.kernel t x y| * ρ y) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
          ((K.integrable_abs_kernel_mul_weight hρ ht x).const_mul B)
          (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [abs_mul]
        calc |K.kernel t x y| * |g y| ≤ |K.kernel t x y| * (B * ρ y) :=
              mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)
          _ = _ := by ring
    _ = B * ∫ y, |K.kernel t x y| * ρ y ∂μ := integral_const_mul _ _
    _ ≤ B * (ρ x * K.weightConst p t) :=
        mul_le_mul_of_nonneg_left (K.integral_abs_kernel_mul_weight_le hρ ht x) hB0
    _ = _ := by ring

/-- The bound `|Q_t g (x)| ≤ B ρ(x) 2^p (M₀ + M_p t^{p/ℓ})` for `|g| ≤ B ρ`. -/
theorem abs_apply_le_of_weight_bound (hρ : K.IsModerateWeight ρ p) {t : ℝ} (ht : 0 < t)
    {g : E → ℝ} {B : ℝ} (hB : ∀ y, |g y| ≤ B * ρ y) (x : E) :
    |K.apply t g x| ≤ B * ρ x * K.weightConst p t := by
  refine le_trans ?_ (K.integral_abs_kernel_mul_le_of_weight_bound hρ ht x hB)
  have := norm_integral_le_integral_norm (μ := μ) (fun y => K.kernel t x y * g y)
  simpa [apply] using this

/-- Uniqueness with weights: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C ρ t^β` for
`0 < t ≤ 1` (`β > 0`) coincide. -/
theorem eq_of_abs_sub_le_weight (hρ : K.IsModerateWeight ρ p) {Λ Λ' : ℝ → E → ℝ}
    (hΛ : Λ ∈ K.distributions) (hΛ' : Λ' ∈ K.distributions) {β C : ℝ} (hβ : 0 < β)
    (h : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x, |Λ t x - Λ' t x| ≤ C * ρ x * t ^ β) : Λ = Λ' := by
  have hD : Λ - Λ' ∈ K.distributions := K.distributions.sub_mem hΛ hΛ'
  have hD' : ∀ t x, (Λ - Λ') t x = Λ t x - Λ' t x := fun _ _ => rfl
  have hshift : ∀ {s t : ℝ}, 0 < s → s < t → ∀ x,
      (Λ - Λ') t x = K.apply (t - s) ((Λ - Λ') s) x := by
    intro s t hs hst x
    rw [K.apply_eq hD (sub_pos.2 hst) hs]
    simp
  have hzero : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x, (Λ - Λ') t x = 0 := by
    intro t ht x
    have hC : 0 ≤ C := by
      have h1 := h 1 ⟨one_pos, le_rfl⟩ x
      have h2 := (abs_nonneg _).trans h1
      simp only [Real.one_rpow, mul_one] at h2
      exact nonneg_of_mul_nonneg_left h2 (hρ.pos x)
    have hle : ∀ s ∈ Set.Ioo (0 : ℝ) t, |(Λ - Λ') t x| ≤
        (C * ρ x * K.weightConst p 1) * s ^ β := by
      intro s hs
      rw [hshift hs.1 hs.2 x]
      have h1 := K.abs_apply_le_of_weight_bound hρ (sub_pos.2 hs.2)
        (g := (Λ - Λ') s) (B := C * s ^ β) (fun y => by
          rw [hD']
          calc |Λ s y - Λ' s y| ≤ C * ρ y * s ^ β := h s ⟨hs.1, hs.2.le.trans ht.2⟩ y
            _ = _ := by ring) x
      refine h1.trans ?_
      have hw := K.weightConst_mono hρ.nonneg_exp (sub_pos.2 hs.2).le
        (show t - s ≤ 1 by linarith [ht.2, hs.1])
      have hn : 0 ≤ C * s ^ β * ρ x :=
        mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hs.1.le _)) (hρ.pos x).le
      calc C * s ^ β * ρ x * K.weightConst p (t - s)
          ≤ C * s ^ β * ρ x * K.weightConst p 1 := mul_le_mul_of_nonneg_left hw hn
        _ = _ := by ring
    have h0 : Tendsto (fun s : ℝ => (C * ρ x * K.weightConst p 1) * s ^ β) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuous_rpow_const hβ.le).const_mul
        (C * ρ x * K.weightConst p 1)).tendsto 0
      rw [Real.zero_rpow hβ.ne', mul_zero] at this
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
