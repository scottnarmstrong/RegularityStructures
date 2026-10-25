/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Moment
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Self-adjointness of `Q_h` against a distribution of local order `γ`

* `integral_mul_apply_eq`: `∫ (Q_h g) φ = ∫ g (Q_h φ)` (Fubini and symmetry of the kernel) when
  `Q_h(y, z) g(z) φ(y)` is integrable on `E × E`;
* `LocalData.integrable_prod`: that integrability holds for `g = Λ_s`, `Λ` of local order `γ` at
  `x₀` and `φ` measurable, integrable and supported in `{d(·, x₀) ≤ λ}`;
* `LocalData.integral_apply_mul`: `∫ Λ_{s+h} φ = ∫ Λ_s (Q_h φ)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `φ` is a test function adapted to `x₀` at scale `λ`: measurable, integrable and vanishing
where `d(y, x₀) > λ`. -/
structure IsSupported (φ : E → ℝ) (x₀ : E) (lam : ℝ) : Prop where
  meas : Measurable φ
  integrable : Integrable φ μ
  supp : ∀ y, lam < K.scaleDist y x₀ → φ y = 0

theorem integral_mul_apply_eq [SFinite μ] (hK : K.IsSymmetric) {h : ℝ} {g φ : E → ℝ}
    (hint : Integrable (fun p : E × E => K.kernel h p.1 p.2 * g p.2 * φ p.1) (μ.prod μ)) :
    ∫ y, K.apply h g y * φ y ∂μ = ∫ z, g z * K.apply h φ z ∂μ := by
  calc ∫ y, K.apply h g y * φ y ∂μ = ∫ y, ∫ z, K.kernel h y z * g z * φ y ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [apply]
        rw [← integral_mul_const]
    _ = ∫ z, ∫ y, K.kernel h y z * g z * φ y ∂μ ∂μ :=
        integral_integral_swap (f := fun y z => K.kernel h y z * g z * φ y) hint
    _ = ∫ z, g z * K.apply h φ z ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [hK h y z]; ring

theorem integrable_mul_apply [SFinite μ] (hK : K.IsSymmetric) {h : ℝ} {g φ : E → ℝ}
    (hint : Integrable (fun p : E × E => K.kernel h p.1 p.2 * g p.2 * φ p.1) (μ.prod μ)) :
    Integrable (fun z => g z * K.apply h φ z) μ := by
  have h1 := hint.swap.integral_prod_left
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp, Prod.swap_prod_mk, apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hK h y z]; ring

end RegularityStructures.RegularisingSemigroup

end
