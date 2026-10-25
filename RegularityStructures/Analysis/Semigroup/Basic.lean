/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularising semigroups and the distributions they see

A *regularising semigroup* on a measure space `(E, μ)` is a family of integral kernels
`Q_t(x, y)`, `t > 0`, with the semigroup property `∫ Q_s(x, z) Q_t(z, y) dz = Q_{s+t}(x, y)` and
the moment bounds `∫ |Q_t(x, y)| d(y, x)^r dy ≤ M_r t^{r/ℓ}`, where `d` is a distance-like size
and `ℓ > 0` the scaling order. This is the setting of [Hos25, Definition 2.6] (properties (i) and
(iii), with the condition (2.2) on `G` integrated against the kernel), specialised to the
unweighted case `w = 1`. The time-derivative bound (iv) of [Hos25] is not part of the interface;
the reconstruction theorem in the representation used here does not need it.

A *`Q`-distribution* is a family `(Λ_t)_{t>0}` of functions on `E` with
`∫ Q_s(x, y) Λ_t(y) dy = Λ_{s+t}(x)`: it records the regularisations `Λ_t = Q_t Λ` of a
distribution `Λ`. A tempered distribution `ξ` gives the family `Λ_t(x) = ⟨ξ, Q_t(x, ·)⟩`, and the
family determines `ξ` because `Q_t φ → φ` for test functions `φ`; for the Besov space
`B^{α,Q}_{∞,∞}` of [Hos25, Definition 2.9] this identification is (2.5) there. Working with the
families directly avoids completions: the reconstruction `Rf` is *defined* as the family
`t ↦ lim_{s↓0} R^t_s f` of [Hos25, proof of Theorem 4.1].

Source: [Hos25] = arXiv:2310.07396v2, §2.3 and §4.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- A regularising semigroup on `(E, μ)`: kernels `Q_t(x, y)` with the semigroup property and
moment bounds `∫ |Q_t(x, y)| d(y, x)^r dμ(y) ≤ M_r t^{r/ℓ}` for every `r ≥ 0` and `t > 0`
([Hos25, Definition 2.6 (i), (iii) and (2.2)], unweighted). -/
structure RegularisingSemigroup (E : Type*) [MeasurableSpace E] (μ : Measure E) where
  /-- The kernel `Q_t(x, y)`. -/
  kernel : ℝ → E → E → ℝ
  /-- The scaling order `ℓ`: regularity `α` corresponds to the size `t^{α/ℓ}`. -/
  order : ℝ
  order_pos : 0 < order
  /-- The size `d(y, x)` of the increment from `x` to `y` (on `ℝ⁴`, the parabolic size
  `‖y - x‖_𝔰`). -/
  scaleDist : E → E → ℝ
  scaleDist_nonneg : ∀ x y, 0 ≤ scaleDist x y
  /-- The moment constants `M_r`. -/
  momentConst : ℝ → ℝ
  momentConst_nonneg : ∀ r, 0 ≤ momentConst r
  measurable_kernel : ∀ t, Measurable (Function.uncurry (kernel t))
  integrable_moment : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    Integrable (fun y => |kernel t x y| * scaleDist y x ^ r) μ
  moment_le : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    ∫ y, |kernel t x y| * scaleDist y x ^ r ∂μ ≤ momentConst r * t ^ (r / order)
  /-- The semigroup property `Q_s Q_t = Q_{s+t}`. -/
  semigroup : ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x y,
    ∫ z, kernel s x z * kernel t z y ∂μ = kernel (s + t) x y

namespace RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The action `(Q_t g)(x) = ∫ Q_t(x, y) g(y) dμ(y)` of the semigroup on functions. -/
def apply (t : ℝ) (g : E → ℝ) (x : E) : ℝ := ∫ y, K.kernel t x y * g y ∂μ

/-- The `Q`-distributions: families `(Λ_t)_{t>0}` of functions with `Q_s Λ_t = Λ_{s+t}`, the
integrals converging absolutely, normalised by `Λ_t = 0` for `t ≤ 0`. `Λ t x` is the
regularisation `(Q_t Λ)(x)` of the distribution `Λ`. -/
def distributions : Submodule ℝ (ℝ → E → ℝ) where
  carrier := {Λ | (∀ ⦃t : ℝ⦄, t ≤ 0 → Λ t = 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x,
      Integrable (fun y => K.kernel s x y * Λ t y) μ ∧ K.apply s (Λ t) x = Λ (s + t) x}
  add_mem' := by
    rintro Λ Λ' ⟨h0, h⟩ ⟨h0', h'⟩
    refine ⟨fun t ht => by simp [h0 ht, h0' ht], fun s t hs ht x => ?_⟩
    obtain ⟨hi, he⟩ := h hs ht x
    obtain ⟨hi', he'⟩ := h' hs ht x
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, mul_add]
      exact hi.add hi'
    simp only [apply, Pi.add_apply, mul_add] at he he' ⊢
    rw [integral_add hi hi', he, he']
  zero_mem' := ⟨fun _ _ => rfl, fun s t _ _ x => by simp [apply]⟩
  smul_mem' := by
    rintro c Λ ⟨h0, h⟩
    refine ⟨fun t ht => by simp [h0 ht], fun s t hs ht x => ?_⟩
    obtain ⟨hi, he⟩ := h hs ht x
    refine ⟨by simpa [mul_left_comm] using hi.const_mul c, ?_⟩
    simp only [apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c] at he ⊢
    rw [integral_const_mul, he]

end RegularisingSemigroup

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem integrable_kernel_mul {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (x : E) : Integrable (fun y => K.kernel s x y * Λ t y) μ :=
  (hΛ.2 hs ht x).1

theorem apply_eq {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : E) : K.apply s (Λ t) x = Λ (s + t) x :=
  (hΛ.2 hs ht x).2

theorem eq_zero_of_nonpos {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {t : ℝ} (ht : t ≤ 0) :
    Λ t = 0 :=
  hΛ.1 ht

end RegularityStructures.RegularisingSemigroup

end
