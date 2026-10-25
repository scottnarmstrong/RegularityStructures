/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Operator

/-!
# The auxiliary semigroup acting on polynomially bounded functions

A measurable function `g` on `ℝ⁴` with `|g(u)| ≤ B (1 + ‖u‖_𝔰)^n` (`PolyBounded g`) is integrable
against every kernel `q_t(y - ·)`, `t > 0` (`integrable_parabolicKernel_mul`), the regularisation
`Q_t g` is again polynomially bounded and measurable (`PolyBounded.apply`), and the semigroup
property `Q_s Q_t g = Q_{s+t} g` holds (`apply_apply_of_polyBounded`, Fubini). This is what is
needed to see polynomials as `Q`-distributions [Hai14, Section 2.2], [Hos25, Definition 2.6].
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

/-- A measurable function of polynomial growth: `|g(u)| ≤ B (1 + ‖u‖_𝔰)^n`. -/
def PolyBounded (g : ParabolicSpace → ℝ) : Prop :=
  Measurable g ∧ ∃ (B : ℝ) (n : ℕ), ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n

/-- The `n`-th kernel moment `∫ |q_t(a)| (1 + ‖a‖_𝔰)^n da`. -/
noncomputable def kernelPowMoment (n : ℕ) (t : ℝ) : ℝ :=
  ∫ a, |parabolicKernel t a| * (1 + parabolicNorm a) ^ n

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem one_add_parabolicNorm_le (u y : ParabolicSpace) :
    1 + parabolicNorm u ≤ (1 + parabolicNorm y) * (1 + parabolicNorm (u - y)) := by
  have h := parabolicNorm_add_le (u - y) y
  rw [sub_add_cancel] at h
  have h1 := parabolicNorm_nonneg y
  have h2 := parabolicNorm_nonneg (u - y)
  have h3 := mul_nonneg h1 h2
  linarith [mul_add (1 + parabolicNorm y) 1 (parabolicNorm (u - y))]

theorem one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) :=
        le_mul_of_one_le_right (pow_nonneg (by norm_num) n) (by linarith [pow_nonneg ha n])
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + a ^ n) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by norm_num) n)

theorem integrable_abs_parabolicKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun a => |parabolicKernel t a|) := by
  simpa using integrable_abs_parabolicKernel_mul_norm ht (le_refl (0 : ℝ))

theorem integrable_abs_parabolicKernel_mul_pow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun a => |parabolicKernel t a| * (1 + parabolicNorm a) ^ n) := by
  have h1 := integrable_abs_parabolicKernel ht
  have h2 := integrable_abs_parabolicKernel_mul_norm ht (Nat.cast_nonneg n)
  simp only [Real.rpow_natCast] at h2
  refine ((h1.add h2).const_mul (2 ^ n)).mono' ?_ (Filter.Eventually.of_forall fun a => ?_)
  · exact ((continuous_abs.measurable.comp (measurable_parabolicKernel t)).mul
      ((measurable_const.add continuous_parabolicNorm.measurable).pow_const n)).aestronglyMeasurable
  · have hn := parabolicNorm_nonneg a
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _))]
    have := mul_le_mul_of_nonneg_left (one_add_pow_le _ hn n) (abs_nonneg (parabolicKernel t a))
    calc |parabolicKernel t a| * (1 + parabolicNorm a) ^ n
        ≤ |parabolicKernel t a| * (2 ^ n * (1 + parabolicNorm a ^ n)) := this
      _ = 2 ^ n * (|parabolicKernel t a| + |parabolicKernel t a| * parabolicNorm a ^ n) := by
        ring

theorem abs_parabolicKernel_mul_pow_le (t : ℝ) (n : ℕ) (y z : ParabolicSpace) :
    |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n ≤
      (1 + parabolicNorm y) ^ n * (|parabolicKernel t (z - y)| * (1 + parabolicNorm (z - y)) ^ n) := by
  have h := one_add_parabolicNorm_le z y
  have hk : parabolicKernel t (z - y) = parabolicKernel t (y - z) := by
    rw [← parabolicKernel_neg t (y - z), neg_sub]
  rw [hk]
  have h0 : 0 ≤ 1 + parabolicNorm z := by linarith [parabolicNorm_nonneg z]
  have := pow_le_pow_left₀ h0 h n
  rw [mul_pow] at this
  calc |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n
      ≤ |parabolicKernel t (y - z)| * ((1 + parabolicNorm y) ^ n * (1 + parabolicNorm (z - y)) ^ n) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring

theorem integrable_abs_kernel_mul_pow {t : ℝ} (ht : 0 < t) (n : ℕ) (y : ParabolicSpace) :
    Integrable (fun z => |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n) := by
  have hF := integrable_abs_parabolicKernel_mul_pow ht n
  have hF' : Integrable (fun a => |parabolicKernel t a| * (1 + parabolicNorm a) ^ n)
      (volume : Measure (ℝ × (Fin 3 → ℝ))) := hF
  rw [Measure.volume_eq_prod] at hF'
  have h : Integrable (fun z : ParabolicSpace => (1 + parabolicNorm y) ^ n *
      (|parabolicKernel t (z - y)| * (1 + parabolicNorm (z - y)) ^ n)) := by
    rw [Measure.volume_eq_prod]
    exact (hF'.comp_sub_right y).const_mul _
  refine h.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (((continuous_abs.measurable.comp ((measurable_parabolicKernel t).comp
      (measurable_const.sub measurable_id)))).mul
      ((measurable_const.add (continuous_parabolicNorm.measurable)).pow_const n)).aestronglyMeasurable
  · have hn := parabolicNorm_nonneg z
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _))]
    exact abs_parabolicKernel_mul_pow_le t n y z

theorem integral_abs_kernel_mul_pow_le {t : ℝ} (ht : 0 < t) (n : ℕ) (y : ParabolicSpace) :
    ∫ z, |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n ≤
      (1 + parabolicNorm y) ^ n * kernelPowMoment n t := by
  have hF := integrable_abs_parabolicKernel_mul_pow ht n
  calc ∫ z, |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n
      ≤ ∫ z, (1 + parabolicNorm y) ^ n *
          (|parabolicKernel t (z - y)| * (1 + parabolicNorm (z - y)) ^ n) :=
        integral_mono (integrable_abs_kernel_mul_pow ht n y)
          (by
            have hF' := hF
            rw [Measure.volume_eq_prod] at hF' ⊢
            exact (hF'.comp_sub_right y).const_mul _)
          (fun z => abs_parabolicKernel_mul_pow_le t n y z)
    _ = (1 + parabolicNorm y) ^ n *
          ∫ z, |parabolicKernel t (z - y)| * (1 + parabolicNorm (z - y)) ^ n :=
        integral_const_mul _ _
    _ = _ := by
        rw [kernelPowMoment]
        congr 1
        rw [Measure.volume_eq_prod]
        exact integral_sub_right_eq_self
          (fun a : ParabolicSpace => |parabolicKernel t a| * (1 + parabolicNorm a) ^ n) y

variable {g : ParabolicSpace → ℝ}

theorem integrable_parabolicKernel_mul_of_bound (hgm : Measurable g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    Integrable (fun z => parabolicKernel t (y - z) * g z) := by
  refine ((integrable_abs_kernel_mul_pow ht n y).const_mul B).mono' ?_
    (Filter.Eventually.of_forall fun z => ?_)
  · exact (((measurable_parabolicKernel t).comp (measurable_const.sub measurable_id)).mul
      hgm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    calc |parabolicKernel t (y - z)| * |g z|
        ≤ |parabolicKernel t (y - z)| * (B * (1 + parabolicNorm z) ^ n) :=
          mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
      _ = _ := by ring

theorem PolyBounded.integrable_parabolicKernel_mul (hg : PolyBounded g) {t : ℝ} (ht : 0 < t)
    (y : ParabolicSpace) : Integrable (fun z => parabolicKernel t (y - z) * g z) := by
  obtain ⟨hm, B, n, hB⟩ := hg
  exact integrable_parabolicKernel_mul_of_bound hm hB ht y

theorem nonneg_of_bound {B : ℝ} {n : ℕ} (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) :
    0 ≤ B := by
  have h := (abs_nonneg _).trans (hB 0)
  rw [parabolicNorm_zero] at h
  simpa using h

theorem integral_abs_parabolicKernel_mul_le (hgm : Measurable g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    ∫ z, |parabolicKernel t (y - z) * g z| ≤ B * ((1 + parabolicNorm y) ^ n * kernelPowMoment n t) := by
  have hB0 := nonneg_of_bound hB
  calc ∫ z, |parabolicKernel t (y - z) * g z|
      ≤ ∫ z, B * (|parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n) := by
        refine integral_mono (integrable_parabolicKernel_mul_of_bound hgm hB ht y).abs
          ((integrable_abs_kernel_mul_pow ht n y).const_mul B) (fun z => ?_)
        rw [abs_mul]
        calc |parabolicKernel t (y - z)| * |g z|
            ≤ |parabolicKernel t (y - z)| * (B * (1 + parabolicNorm z) ^ n) :=
              mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
          _ = _ := by ring
    _ = B * ∫ z, |parabolicKernel t (y - z)| * (1 + parabolicNorm z) ^ n := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_kernel_mul_pow_le ht n y) hB0

theorem PolyBounded.apply (hg : PolyBounded g) {t : ℝ} (ht : 0 < t) :
    PolyBounded (parabolicSemigroup.apply t g) := by
  obtain ⟨hm, B, n, hB⟩ := hg
  refine ⟨parabolicSemigroup.measurable_apply t hm, B * kernelPowMoment n t, n, fun y => ?_⟩
  calc |parabolicSemigroup.apply t g y|
      ≤ ∫ z, |parabolicKernel t (y - z) * g z| := abs_integral_le_integral_abs
    _ ≤ B * ((1 + parabolicNorm y) ^ n * kernelPowMoment n t) :=
        integral_abs_parabolicKernel_mul_le hm hB ht y
    _ = _ := by ring

end RegularityStructures

end
