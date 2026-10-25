/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4Convolution
public import RegularityStructures.Abstract.QFamilyR4RescaledTest

/-!
# Test-function pairings determine `Q`-families on `ℝ⁴`

An *admissible* `Q`-family for the auxiliary semigroup on `ℝ⁴` is `Λ ∈ distributions` with
measurable regularisations and a Besov-type bound `|Λ_u| ≤ C u^{α/4}` for `0 < u ≤ 1`, `α > -4`
([Hos25, Definition 2.9], `p = q = ∞`). For such families the pairing
`⟨Λ, φ^λ_x⟩ = lim_{s↓0} ∫ Λ_s φ^λ_x` with every rescaled test function exists
(`tendsto_integral_rescaledTestFunction`), and:

* `eq_zero_of_abs_pairing_rescaledTestFunction_le`: **if `|⟨D, φ^λ_w⟩| ≤ ε(λ)` for all
  `0 < λ ≤ 1` and all `w`, for one `φ ∈ B^4` with `∫ φ ≠ 0` and some `ε(λ) → 0`, then `D = 0`.**
  (Proof: `∫ φ^λ_0(v) D_t(x + v) dv = ∫ q_t(x − w) ⟨D, φ^λ_w⟩ dw` is at most `M₀ ε(λ)`, and it
  tends to `(∫ φ) D_t(x)` as `λ ↓ 0` because `D_t` is continuous.) This is the form of the
  uniqueness statement used in [Hai14, Theorem 3.10] ("if `γ > 0`, (3.3) defines `Rf`
  uniquely"), with `ε(λ) = C λ^γ`.
* `eq_of_pairing_rescaledTestFunction_eq` (**Q1**): two admissible `Q`-families with the same
  pairings `⟨Λ, φ^λ_x⟩ = ⟨Λ', φ^λ_x⟩` for all `0 < λ ≤ 1` and `x`, for one `φ ∈ B^4` with
  `∫ φ ≠ 0`, are equal; `eq_of_forall_pairing_rescaledTestFunction_eq`: the same with the
  pairings against all of `B^4`.

Source: [Hai14, Theorem 3.10], [Hos25, Section 2.3].
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

attribute [local instance] isAddHaarMeasure_volume_parabolicSpace

variable {D : ℝ → ParabolicSpace → ℝ}

/-- `|∫ φ^c_0(v) D_t(x + v) dv| ≤ M₀ ε` when all pairings `⟨D, φ^c_w⟩` are bounded by `ε`. -/
theorem abs_integral_rescaledTestFunction_mul_le (hD : D ∈ parabolicSemigroup.distributions)
    (hDm : ∀ u, 0 < u → Measurable (D u)) {α C : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |D u y| ≤ C * u ^ (α / 4)) {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) {ε : ℝ}
    (hε : ∀ w, |parabolicSemigroup.pairing D (rescaledTestFunction φ c w)| ≤ ε) :
    |∫ v, rescaledTestFunction φ c 0 v * D t (x + v)| ≤ parabolicSemigroup.momentConst 0 * ε := by
  rw [integral_rescaledTestFunction_mul_eq hD hDm hα hb hφ hc ht x]
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε x)
  have hq : Integrable (parabolicKernel t) := integrable_parabolicKernel ht
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((hq.comp_sub_left x).abs.mul_const ε)
    (Eventually.of_forall fun w => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hε w) (abs_nonneg _)
  · rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (parabolicSemigroup.integral_abs_kernel_le ht x) hε0

/-- Mollifier limit: for a bounded measurable `f` continuous at `x` (in the parabolic size),
`∫ φ^c_0(v) f(x + v) dv → (∫ φ) f(x)` as `c ↓ 0`. -/
theorem tendsto_integral_rescaledTestFunction_mul {f : ParabolicSpace → ℝ} (hfm : Measurable f)
    {B : ℝ} (hfb : ∀ y, |f y| ≤ B) {x : ParabolicSpace}
    (hfc : ∀ ε > 0, ∃ δ > 0, ∀ y, parabolicNorm (y - x) < δ → |f y - f x| < ε)
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) :
    Tendsto (fun c => ∫ v, rescaledTestFunction φ c 0 v * f (x + v)) (𝓝[>] 0)
      (𝓝 ((∫ v, φ v) * f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hfc (ε / 32) (by positivity)
  refine ⟨δ, hδ, fun {c} hc hcδ => ?_⟩
  have hc0 : (0 : ℝ) < c := hc
  have hcδ' : c < δ := by simpa [Real.dist_eq, abs_of_pos hc0] using hcδ
  have hρi : Integrable (rescaledTestFunction φ c 0) := integrable_rescaledTestFunction hφ hc0 0
  have hfi : Integrable fun v => rescaledTestFunction φ c 0 v * f (x + v) :=
    hρi.mul_bdd (hfm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hfb _)
  have e : (∫ v, rescaledTestFunction φ c 0 v * f (x + v)) - (∫ v, φ v) * f x =
      ∫ v, rescaledTestFunction φ c 0 v * (f (x + v) - f x) := by
    rw [← integral_rescaledTestFunction φ hc0 0, ← integral_mul_const, ← integral_sub hfi
      (hρi.mul_const _)]
    simp only [mul_sub]
  rw [Real.dist_eq, e, ← Real.norm_eq_abs]
  have hpt : ∀ v, ‖rescaledTestFunction φ c 0 v * (f (x + v) - f x)‖ ≤
      |rescaledTestFunction φ c 0 v| * (ε / 32) := by
    intro v
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hv : c < parabolicNorm (v - 0)
    · rw [rescaledTestFunction_eq_zero hφ.2.1 hc0 hv]
      simp
    · refine mul_le_mul_of_nonneg_left (hfδ (x + v) ?_).le (abs_nonneg _)
      rw [add_sub_cancel_left]
      rw [sub_zero] at hv
      exact (not_lt.1 hv).trans_lt hcδ'
  refine (norm_integral_le_of_norm_le (hρi.abs.mul_const _) (Eventually.of_forall hpt)).trans_lt ?_
  rw [integral_mul_const]
  have h16 := integral_abs_rescaledTestFunction_le hφ hc0 0
  calc (∫ v, |rescaledTestFunction φ c 0 v|) * (ε / 32) ≤ 16 * (ε / 32) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
    _ < ε := by linarith

/-- **Uniqueness from test-function bounds**: if an admissible `Q`-family `D` on `ℝ⁴` has
`|⟨D, φ^λ_w⟩| ≤ ε(λ)` for all `0 < λ ≤ 1` and all `w`, for one `φ ∈ B^4` with `∫ φ ≠ 0` and some
`ε(λ) → 0` as `λ ↓ 0`, then `D = 0`. -/
theorem eq_zero_of_abs_pairing_rescaledTestFunction_le
    (hD : D ∈ parabolicSemigroup.distributions) (hDm : ∀ u, 0 < u → Measurable (D u))
    {α C : ℝ} (hα : -4 < α) (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |D u y| ≤ C * u ^ (α / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0)
    {ε : ℝ → ℝ} (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (h : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ w,
      |parabolicSemigroup.pairing D (rescaledTestFunction φ c w)| ≤ ε c) :
    D = 0 := by
  funext t x
  rcases le_or_gt t 0 with ht | ht
  · rw [parabolicSemigroup.eq_zero_of_nonpos hD ht]
    rfl
  have hDb : ∀ u, 0 < u → ∃ B, ∀ y, |D u y| ≤ B := fun u hu =>
    parabolicSemigroup.exists_bound_of_besov hD hb hu
  obtain ⟨Bt, hBt⟩ := hDb t ht
  have hcont : ∀ ε > 0, ∃ δ > 0, ∀ y, parabolicNorm (y - x) < δ → |D t y - D t x| < ε :=
    RegularisingSemigroup.continuous_scaleDist parabolicSemigroup_isStrongFeller hD hDm hDb ht x
  have h1 := tendsto_integral_rescaledTestFunction_mul (hDm t ht) hBt hcont hφ
  have h2 : Tendsto (fun c => parabolicSemigroup.momentConst 0 * ε c) (𝓝[>] 0) (𝓝 0) := by
    simpa using hε.const_mul (parabolicSemigroup.momentConst 0)
  have hle : |(∫ v, φ v) * D t x| ≤ 0 := le_of_tendsto_of_tendsto h1.abs h2
    (Filter.mem_of_superset (Ioc_mem_nhdsGT one_pos) fun c hc =>
      abs_integral_rescaledTestFunction_mul_le hD hDm hα hb hφ hc.1 ht x (h c hc))
  exact (mul_eq_zero.1 (abs_nonpos_iff.1 hle)).resolve_left hφ0

/-- A Besov-type `Q`-family has bounded measurable regularisations, so its products with
integrable functions are integrable. -/
theorem integrable_mul_of_besov {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {α C : ℝ} (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    {ψ : ParabolicSpace → ℝ} (hψ : Integrable ψ) {s : ℝ} (hs : 0 < s) :
    Integrable fun y => Λ s y * ψ y := by
  obtain ⟨B, hB⟩ := parabolicSemigroup.exists_bound_of_besov hΛ hb hs
  exact hψ.bdd_mul (hΛm s hs).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)

/-- The difference of two Besov-type `Q`-families is of Besov type, with the smaller exponent. -/
theorem besov_sub {Λ Λ' : ℝ → ParabolicSpace → ℝ} {α α' C C' : ℝ}
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    (hb' : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ' u y| ≤ C' * u ^ (α' / 4)) :
    ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |(Λ - Λ') u y| ≤ (C + C') * u ^ (min α α' / 4) := by
  have hC := RegularisingSemigroup.nonneg_of_besov (K := parabolicSemigroup) hb 0
  have hC' := RegularisingSemigroup.nonneg_of_besov (K := parabolicSemigroup) hb' 0
  intro u hu y
  have e1 : u ^ (α / 4) ≤ u ^ (min α α' / 4) := Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have e2 : u ^ (α' / 4) ≤ u ^ (min α α' / 4) := Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  calc |(Λ - Λ') u y| = |Λ u y - Λ' u y| := rfl
    _ ≤ |Λ u y| + |Λ' u y| := abs_sub _ _
    _ ≤ C * u ^ (α / 4) + C' * u ^ (α' / 4) := add_le_add (hb u hu y) (hb' u hu y)
    _ ≤ C * u ^ (min α α' / 4) + C' * u ^ (min α α' / 4) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC) (mul_le_mul_of_nonneg_left e2 hC')
    _ = (C + C') * u ^ (min α α' / 4) := by ring

/-- The pairing of the difference of two admissible `Q`-families with `φ^c_w` is the difference
of the pairings. -/
theorem pairing_sub_rescaledTestFunction {Λ Λ' : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛ' : Λ' ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) (hΛ'm : ∀ u, 0 < u → Measurable (Λ' u))
    {α α' C C' : ℝ} (hα : -4 < α) (hα' : -4 < α')
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    (hb' : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ' u y| ≤ C' * u ^ (α' / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c)
    (w : ParabolicSpace) :
    parabolicSemigroup.pairing (Λ - Λ') (rescaledTestFunction φ c w) =
      parabolicSemigroup.pairing Λ (rescaledTestFunction φ c w) -
        parabolicSemigroup.pairing Λ' (rescaledTestFunction φ c w) :=
  parabolicSemigroup.pairing_sub
    (fun _ hs => integrable_mul_of_besov hΛ hΛm hb (integrable_rescaledTestFunction hφ hc w) hs)
    (fun _ hs => integrable_mul_of_besov hΛ' hΛ'm hb' (integrable_rescaledTestFunction hφ hc w) hs)
    (tendsto_integral_rescaledTestFunction hΛ hΛm hα hb hφ hc w)
    (tendsto_integral_rescaledTestFunction hΛ' hΛ'm hα' hb' hφ hc w)

/-- **Q1: an admissible `Q`-family on `ℝ⁴` is determined by its pairings with rescaled test
functions.** If `⟨Λ, φ^λ_x⟩ = ⟨Λ', φ^λ_x⟩` for all `0 < λ ≤ 1` and all `x`, for one `φ ∈ B^4`
with `∫ φ ≠ 0`, then `Λ = Λ'`. -/
theorem eq_of_pairing_rescaledTestFunction_eq {Λ Λ' : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛ' : Λ' ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) (hΛ'm : ∀ u, 0 < u → Measurable (Λ' u))
    {α α' C C' : ℝ} (hα : -4 < α) (hα' : -4 < α')
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    (hb' : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ' u y| ≤ C' * u ^ (α' / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0)
    (h : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, parabolicSemigroup.pairing Λ (rescaledTestFunction φ c x) =
      parabolicSemigroup.pairing Λ' (rescaledTestFunction φ c x)) :
    Λ = Λ' := by
  have hD : Λ - Λ' ∈ parabolicSemigroup.distributions :=
    parabolicSemigroup.distributions.sub_mem hΛ hΛ'
  have hDm : ∀ u, 0 < u → Measurable ((Λ - Λ') u) := fun u hu => (hΛm u hu).sub (hΛ'm u hu)
  have h0 := eq_zero_of_abs_pairing_rescaledTestFunction_le hD hDm (lt_min hα hα')
    (besov_sub hb hb') hφ hφ0 (ε := fun _ => 0) tendsto_const_nhds fun c hc w => by
      rw [pairing_sub_rescaledTestFunction hΛ hΛ' hΛm hΛ'm hα hα' hb hb' hφ hc.1 w, h c hc w,
        sub_self, abs_zero]
  exact sub_eq_zero.1 h0

/-- **Q1, all test functions**: admissible `Q`-families on `ℝ⁴` with the same pairings against
every rescaled test function `φ^λ_x`, `φ ∈ B^4`, `0 < λ ≤ 1`, are equal. -/
theorem eq_of_forall_pairing_rescaledTestFunction_eq {Λ Λ' : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛ' : Λ' ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) (hΛ'm : ∀ u, 0 < u → Measurable (Λ' u))
    {α α' C C' : ℝ} (hα : -4 < α) (hα' : -4 < α')
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4))
    (hb' : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ' u y| ≤ C' * u ^ (α' / 4))
    (h : ∀ φ ∈ testFunctionClass 4, ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x,
      parabolicSemigroup.pairing Λ (rescaledTestFunction φ c x) =
        parabolicSemigroup.pairing Λ' (rescaledTestFunction φ c x)) :
    Λ = Λ' := by
  obtain ⟨φ, hφ, hφ0⟩ := exists_mem_testFunctionClass 4
  exact eq_of_pairing_rescaledTestFunction_eq hΛ hΛ' hΛm hΛ'm hα hα' hb hb' hφ hφ0.ne'
    (h φ hφ)

end RegularityStructures

end
