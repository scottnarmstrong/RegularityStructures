/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Consistency
public import RegularityStructures.Analysis.Semigroup.ConsistencyLimit

/-!
# A `Q`-family is its pairing with the kernel functions

A `Q`-family `Λ ∈ K.distributions` records the regularisations `Λ_t = Q_t Λ` of a distribution.
This file makes precise the reading `Λ_t(x) = ⟨Λ, Q_t(x, ·)⟩` and
deduces that a `Q`-family is determined by its pairings with the kernel functions.

* `integral_mul_kernel_eq`: `∫ Λ_s(y) Q_t(x, y) dy = Λ_{t+s}(x)` (the semigroup relation, no
  hypothesis on the kernel);
* `IsStrongFeller`: `Q_t` maps bounded measurable functions to functions that are continuous with
  respect to `scaleDist` (true for the auxiliary semigroup on `ℝ⁴`,
  `parabolicSemigroup_isStrongFeller`);
* `exists_bound_of_besov`: the Besov-type bound `|Λ_t| ≤ C t^{α/ℓ}` (`0 < t ≤ 1`) bounds every
  `Λ_t`, `t > 0`;
* `continuous_scaleDist`, `tendsto_add_nhdsGT`: for a strong Feller semigroup, `Λ_t` is continuous
  and, if the kernel is conservative, `t ↦ Λ_t(x)` is right-continuous;
* `pairing_kernel`: `⟨Λ, Q_t(x, ·)⟩ = Λ_t(x)`;
* `eq_of_pairing_kernel_eq`: two `Q`-families with the same pairings against all kernel functions
  `Q_t(x, ·)` coincide.

The admissibility hypotheses on `Λ` are explicit: `Λ ∈ K.distributions`, each `Λ_t` (`t > 0`)
measurable and bounded.

Source: [Hos25, Section 2.3 (identity (2.5), Remark 2.10)].
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The strong Feller property (in the `scaleDist` topology): for `t > 0`, `Q_t g` is continuous
with respect to `scaleDist` at every point, for every bounded measurable `g`. -/
def IsStrongFeller : Prop :=
  ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃g : E → ℝ⦄, Measurable g → ∀ ⦃B : ℝ⦄, (∀ y, |g y| ≤ B) →
    ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, K.scaleDist y x < δ → |K.apply t g y - K.apply t g x| < ε

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The semigroup relation read as a pairing: `∫ Λ_s(y) Q_t(x, y) dy = Λ_{t+s}(x)`. -/
theorem integral_mul_kernel_eq {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (x : E) :
    ∫ y, Λ s y * K.kernel t x y ∂μ = Λ (t + s) x := by
  rw [← K.apply_eq hΛ ht hs x]
  simp only [apply, mul_comm]

/-- The Besov-type bound `|Λ_t(x)| ≤ C t^{α/ℓ}` for `0 < t ≤ 1` bounds `Λ_t` for every `t > 0`
(for `t > 1`, `Λ_t = Q_{t-1} Λ_1`). -/
theorem exists_bound_of_besov {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {α C : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x| ≤ C * t ^ (α / K.order)) {t : ℝ} (ht : 0 < t) :
    ∃ B, ∀ x, |Λ t x| ≤ B := by
  rcases le_or_gt t 1 with ht1 | ht1
  · exact ⟨C * t ^ (α / K.order), hb t ⟨ht, ht1⟩⟩
  · refine ⟨K.momentConst 0 * C, fun x => ?_⟩
    have h1 : ∀ y, |Λ 1 y| ≤ C := fun y => by
      simpa using hb 1 ⟨one_pos, le_rfl⟩ y
    have e : Λ t x = K.apply (t - 1) (Λ 1) x := by
      rw [K.apply_eq hΛ (sub_pos.2 ht1) one_pos x, sub_add_cancel]
    rw [e]
    exact K.abs_apply_le_of_bound (sub_pos.2 ht1) h1 x

variable {K}

/-- For a strong Feller semigroup, `Λ_t` (`t > 0`) is continuous with respect to `scaleDist`. -/
theorem continuous_scaleDist (hF : K.IsStrongFeller) {Λ : ℝ → E → ℝ}
    (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) {t : ℝ} (ht : 0 < t) (x : E) :
    ∀ ε > 0, ∃ δ > 0, ∀ y, K.scaleDist y x < δ → |Λ t y - Λ t x| < ε := by
  have ht2 : 0 < t / 2 := half_pos ht
  obtain ⟨B, hB⟩ := hΛb (t / 2) ht2
  have e : ∀ y, Λ t y = K.apply (t / 2) (Λ (t / 2)) y := fun y => by
    rw [K.apply_eq hΛ ht2 ht2 y, add_halves]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hF ht2 (hΛm _ ht2) hB x ε hε
  exact ⟨δ, hδ, fun y hy => by rw [e y, e x]; exact h y hy⟩

/-- Right-continuity in time: for a conservative strong Feller semigroup, `Λ_{t+s}(x) → Λ_t(x)`
as `s ↓ 0`. -/
theorem tendsto_add_nhdsGT (hC : K.IsConservative) (hF : K.IsStrongFeller)
    {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) {t : ℝ} (ht : 0 < t) (x : E) :
    Tendsto (fun s => Λ (t + s) x) (𝓝[>] 0) (𝓝 (Λ t x)) := by
  obtain ⟨B, hB⟩ := hΛb t ht
  refine (K.tendsto_apply_nhdsGT hC (hΛm t ht) hB x
    (continuous_scaleDist hF hΛ hΛm hΛb ht x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [K.apply_eq hΛ hs ht x, add_comm]

/-- `∫ Λ_s(y) Q_t(x, y) dy → Λ_t(x)` as `s ↓ 0`. -/
theorem tendsto_integral_mul_kernel (hC : K.IsConservative) (hF : K.IsStrongFeller)
    {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) {t : ℝ} (ht : 0 < t) (x : E) :
    Tendsto (fun s => ∫ y, Λ s y * K.kernel t x y ∂μ) (𝓝[>] 0) (𝓝 (Λ t x)) := by
  refine (tendsto_add_nhdsGT hC hF hΛ hΛm hΛb ht x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (K.integral_mul_kernel_eq hΛ hs ht x).symm

/-- **`Λ_t(x) = ⟨Λ, Q_t(x, ·)⟩`**: the regularisation of a `Q`-family is its pairing with the
kernel function `Q_t(x, ·)` ([Hos25, (2.5)]). -/
theorem pairing_kernel (hC : K.IsConservative) (hF : K.IsStrongFeller)
    {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) {t : ℝ} (ht : 0 < t) (x : E) :
    K.pairing Λ (K.kernel t x) = Λ t x :=
  K.pairing_eq_of_tendsto (tendsto_integral_mul_kernel hC hF hΛ hΛm hΛb ht x)

/-- **A `Q`-family is determined by its pairings with the kernel functions**: two `Q`-families
with measurable, bounded regularisations and `⟨Λ, Q_t(x, ·)⟩ = ⟨Λ', Q_t(x, ·)⟩` for all `t > 0`
and `x` coincide. -/
theorem eq_of_pairing_kernel_eq (hC : K.IsConservative) (hF : K.IsStrongFeller)
    {Λ Λ' : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) (hΛ' : Λ' ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) (hΛ'm : ∀ u, 0 < u → Measurable (Λ' u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) (hΛ'b : ∀ u, 0 < u → ∃ B, ∀ y, |Λ' u y| ≤ B)
    (h : ∀ t, 0 < t → ∀ x, K.pairing Λ (K.kernel t x) = K.pairing Λ' (K.kernel t x)) :
    Λ = Λ' := by
  funext t x
  rcases le_or_gt t 0 with ht | ht
  · rw [K.eq_zero_of_nonpos hΛ ht, K.eq_zero_of_nonpos hΛ' ht]
  · rw [← pairing_kernel hC hF hΛ hΛm hΛb ht x, h t ht x, pairing_kernel hC hF hΛ' hΛ'm hΛ'b ht x]

end RegularityStructures.RegularisingSemigroup

end
