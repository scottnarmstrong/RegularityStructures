/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyKernelPairing
public import RegularityStructures.Analysis.Semigroup.Pairing
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit

/-!
# Pairing of a Besov-type `Q`-family with test functions

The admissible `Q`-families of the bridge to test functions are those with the Besov-type bound
`|Λ_u(y)| ≤ C u^{α/ℓ}` for `0 < u ≤ 1`, `α > -ℓ` ([Hos25, Definition 2.9] with `p = q = ∞`,
`w = 1`), and measurable regularisations. Such a `Λ` is of local order `α` at every point with
exponent set `{α}` (`isLocalOrder_of_besov`), so the pairing machinery of
`Analysis/Semigroup/Pairing/` applies to every test function `φ` supported in a ball
`{d(·, x₀) ≤ R}` (any radius `R > 0`) with generator image `ψ = Lφ` supported there:

* `tendsto_integral_pairing_of_besov`: `∫ Λ_s φ → ⟨Λ, φ⟩` as `s ↓ 0`;
* `abs_integral_le_of_besov`: the uniform bound
  `|∫ Λ_s φ| ≤ C (∫ |φ| + ℓ/(α + ℓ) ∫ |ψ|)` for `0 < s ≤ 1`;
* `abs_pairing_le_of_besov`: the same bound for `⟨Λ, φ⟩`.

Source: [Hos25, Section 2.3], [Hai14, proof of Theorem 3.10].
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

/-- A Besov-type bound `|Λ_u| ≤ C u^{α/ℓ}` is a local order `α` bound at every point, with the
single exponent `α`. -/
theorem isLocalOrder_of_besov {Λ : ℝ → E → ℝ} {α C : ℝ}
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order)) (x₀ : E) :
    K.IsLocalOrder Λ x₀ α {α} C := by
  intro u hu y
  simpa [Finset.sum_singleton, sub_self, Real.rpow_zero, mul_one] using hb u hu y

theorem localData_of_besov {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order)) (x₀ : E) :
    K.LocalData Λ x₀ α {α} C :=
  ⟨hΛ, hΛm, hC, fun _ ha => (Finset.mem_singleton.1 ha).le, isLocalOrder_of_besov hb x₀⟩

/-- The constant of a Besov-type bound is nonnegative (as soon as `E` is nonempty). -/
theorem nonneg_of_besov {Λ : ℝ → E → ℝ} {α C : ℝ}
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order)) (x₀ : E) : 0 ≤ C := by
  have := (abs_nonneg _).trans (hb 1 ⟨one_pos, le_rfl⟩ x₀)
  simpa using this

/-- `R^ℓ` normalisation of the generator bound: `∫|ψ| ≤ (∫|ψ| R^ℓ) R^{-ℓ}`. -/
theorem integral_abs_le_mul_rpow_neg (ψ : E → ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ y, |ψ y| ∂μ ≤ ((∫ y, |ψ y| ∂μ) * R ^ K.order) * R ^ (-K.order) := by
  rw [mul_assoc, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]

theorem incrBound_singleton_one {α : ℝ} (hα : -K.order < α) (R β : ℝ) :
    K.incrBound {α} α R β 1 = β * (K.order / (α + K.order)) := by
  have hℓ := K.order_pos
  have hpos : α + K.order ≠ 0 := by linarith
  simp only [incrBound, Finset.sum_singleton, Real.one_rpow, sub_self, Real.rpow_zero, mul_one]
  congr 1
  field_simp

variable [SFinite μ]

/-- **Uniform bound** for a Besov-type `Q`-family against a test function `φ` supported in
`{d(·, x₀) ≤ R}` with generator image `ψ`: `|∫ Λ_s φ| ≤ C (∫ |φ| + ℓ/(α + ℓ) ∫ |ψ|)` for
`0 < s ≤ 1`. -/
theorem abs_integral_le_of_besov (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α C : ℝ} (hα : -K.order < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order))
    {φ ψ : E → ℝ} {x₀ : E} {R : ℝ} (hR : 0 < R) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hgen : K.IsGeneratorPair φ ψ) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    |∫ y, Λ s y * φ y ∂μ| ≤
      C * ((∫ y, |φ y| ∂μ) + K.order / (α + K.order) * ∫ y, |ψ y| ∂μ) := by
  have hC := nonneg_of_besov hb x₀
  have hℓ := K.order_pos
  have hL := localData_of_besov hΛ hΛm hC hb x₀
  have hq : 0 ≤ K.order / (α + K.order) := div_nonneg hℓ.le (by linarith)
  have hψ0 : 0 ≤ ∫ y, |ψ y| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have h1 : |∫ y, Λ 1 y * φ y ∂μ| ≤ C * ∫ y, |φ y| ∂μ := by
    have := hL.abs_integral_mul_le ⟨one_pos, le_rfl⟩ hφ
    simpa using this
  rcases hs.2.lt_or_eq with hs1 | hs1
  · have hB₁ : 0 ≤ (∫ y, |ψ y| ∂μ) * R ^ K.order :=
      mul_nonneg hψ0 (Real.rpow_nonneg hR.le _)
    have h2 := hL.abs_integral_sub_le hK hd hJ (fun a ha => by
        rw [Finset.mem_singleton.1 ha]; exact hα) hR hB₁ hφ hψ hgen
      (integral_abs_le_mul_rpow_neg ψ hR) hs.1 hs1 le_rfl
    rw [incrBound_singleton_one hα R, mul_assoc ((∫ y, |ψ y| ∂μ)), ← Real.rpow_add hR,
      add_neg_cancel, Real.rpow_zero, mul_one] at h2
    calc |∫ y, Λ s y * φ y ∂μ|
        = |(∫ y, Λ 1 y * φ y ∂μ) - ((∫ y, Λ 1 y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ)| := by
          congr 1; ring
      _ ≤ |∫ y, Λ 1 y * φ y ∂μ| + |(∫ y, Λ 1 y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ| :=
          abs_sub _ _
      _ ≤ C * ∫ y, |φ y| ∂μ + C * (∫ y, |ψ y| ∂μ) * (K.order / (α + K.order)) :=
          add_le_add h1 h2
      _ = _ := by ring
  · subst hs1
    refine h1.trans ?_
    have : 0 ≤ C * (K.order / (α + K.order) * ∫ y, |ψ y| ∂μ) :=
      mul_nonneg hC (mul_nonneg hq hψ0)
    linarith [mul_add C (∫ y, |φ y| ∂μ) (K.order / (α + K.order) * ∫ y, |ψ y| ∂μ)]

/-- **Existence of the pairing** of a Besov-type `Q`-family (`α > -ℓ`) with a test function
supported in `{d(·, x₀) ≤ R}` whose generator image is supported there. -/
theorem tendsto_integral_pairing_of_besov (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α C : ℝ} (hα : -K.order < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order))
    {φ ψ : E → ℝ} {x₀ : E} {R : ℝ} (hR : 0 < R) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hgen : K.IsGeneratorPair φ ψ) :
    Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 (K.pairing Λ φ)) := by
  have hC := nonneg_of_besov hb x₀
  have hL := localData_of_besov hΛ hΛm hC hb x₀
  have hB₁ : 0 ≤ (∫ y, |ψ y| ∂μ) * R ^ K.order :=
    mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (Real.rpow_nonneg hR.le _)
  obtain ⟨L, hL⟩ := hL.exists_tendsto_integral hK hd hJ (fun a ha => by
    rw [Finset.mem_singleton.1 ha]; exact hα) hR hB₁ hφ hψ hgen
    (integral_abs_le_mul_rpow_neg ψ hR)
  rwa [K.pairing_eq_of_tendsto hL]

/-- The bound of `abs_integral_le_of_besov` for the pairing `⟨Λ, φ⟩`. -/
theorem abs_pairing_le_of_besov (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α C : ℝ} (hα : -K.order < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / K.order))
    {φ ψ : E → ℝ} {x₀ : E} {R : ℝ} (hR : 0 < R) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hgen : K.IsGeneratorPair φ ψ) :
    |K.pairing Λ φ| ≤ C * ((∫ y, |φ y| ∂μ) + K.order / (α + K.order) * ∫ y, |ψ y| ∂μ) :=
  le_of_tendsto (tendsto_integral_pairing_of_besov hK hd hJ hΛ hΛm hα hb hR hφ hψ hgen).abs
    (Filter.mem_of_superset (Ioc_mem_nhdsGT one_pos) fun _ hs =>
      abs_integral_le_of_besov hK hd hJ hΛ hΛm hα hb hR hφ hψ hgen hs)

end RegularityStructures.RegularisingSemigroup

end
