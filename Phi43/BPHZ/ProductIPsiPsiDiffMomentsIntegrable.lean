/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiLatticeReduce

/-!
# Integrability of the reduced lattice integrand of a recentred-product field

If `Q_t(x, ·) (I(Ψ) Φ)` is integrable on `ℝ⁴`, then the reduced integrand
`u ↦ ((∫ k(u, w) Ψ(w) dw) Φ(u) + 0) g(u)` is integrable on `ℝ × T³`
(companion of `integral_semigroup_mul_iPsi_field_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Integrability of the reduced integrand on `ℝ × T³`.** -/
theorem integrable_latticeIntegrand_of_integrable_semigroup_mul_iPsi_field
    {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    {N : ℕ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (x' : SpaceTime) (t' : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x' t' a w| ≤ L * (1 + ∑ i, |a i|))
    (hξ : IsSmoothOnSpaceTime (ξ ω)) {Φ : SpaceTime → ℝ} (hΦ : Measurable Φ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace)
    (hint : Integrable fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      (hairerIPsiRecentred N ξ ω x y * Φ (spaceTimeProj y))) :
    Integrable fun u => ((∫ w, latticeK N t x u w * hairerPsiField N ξ ω w) * Φ u + 0) *
      latticeG t x u := by
  have hv : Measurable fun y : ParabolicSpace => hairerIPsiRecentred N ξ ω x y :=
    (continuous_hairerIPsiRecentred_right N ω hξ x).measurable
  have hm : Measurable fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      (hairerIPsiRecentred N ξ ω x y * Φ (spaceTimeProj y)) :=
    (measurable_parabolicSemigroup_kernel t x).mul
      (hv.mul (hΦ.comp continuous_spaceTimeProj.measurable))
  refine (integrable_and_integral_tsum_latticeLift hm hint).1.congr ?_
  have hΨc : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  filter_upwards [ae_latticeWeightSum_lt_top ht x] with u hu
  have h1 := tsum_latticeQ_mul_integral hL0 hL hΨc t x hu
  have e : ∀ n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
      (hairerIPsiRecentred N ξ ω x (latticeLift u n) * Φ (spaceTimeProj (latticeLift u n))) =
      (parabolicSemigroup.kernel t x (latticeLift u n) *
        ∫ w, hairerTaylorKernelAt N x (latticeLift u n) w * hairerPsiField N ξ ω w) * Φ u := by
    intro n
    rw [hairerIPsiRecentred_eq_integral_taylorKernelAt N hξ, spaceTimeProj_latticeLift]
    ring
  simp_rw [e]
  rw [tsum_mul_right, h1]
  ring

end RegularityStructures.Phi43

end
