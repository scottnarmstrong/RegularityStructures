/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Fubini

/-!
# The increment identity (`LocalBall` version)
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

/-- [Hai14, proof of Theorem 3.10]: `∫ Λ_T φ - ∫ Λ_s φ = ∫_s^T ∫ Λ_u ψ du` for `0 < s < T ≤ 1`. -/
theorem LocalBall.integral_sub_integral_eq_integral [SFinite μ] (hK : K.IsSymmetric) (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam) {φ ψ : E → ℝ} 
    (hφ : K.IsSupported φ x₀ lam) (hψ : K.IsSupported ψ x₀ lam) (hgen : K.IsGeneratorPair φ ψ)
    {s T : ℝ} (hs : 0 < s) (hsT : s < T) (hT : T ≤ 1) :
    ∫ y, Λ T y * φ y ∂μ - ∫ y, Λ s y * φ y ∂μ = ∫ u in s..T, ∫ y, Λ u y * ψ y ∂μ := by
  have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs, hsT.le.trans hT⟩
  have hh : 0 < T - s := sub_pos.2 hsT
  have hTs : s + (T - s) = T := by ring
  have h1 : ∫ y, Λ T y * φ y ∂μ - ∫ y, Λ s y * φ y ∂μ =
      ∫ z, Λ s z * (K.apply (T - s) φ z - φ z) ∂μ := by
    have := hΛ.integral_apply_mul hK hs' hφ hh
    rw [hTs] at this
    rw [this, ← integral_sub (hΛ.integrable_mul_apply hK hs' hφ hh) (hΛ.integrable_mul hs' hφ)]
    simp only [mul_sub]
  have h2 : ∫ z, Λ s z * (K.apply (T - s) φ z - φ z) ∂μ =
      ∫ v in (0 : ℝ)..(T - s), ∫ z, Λ s z * K.apply v ψ z ∂μ := by
    have hint := hΛ.integrable_uncurry_apply hK hJ hs' hψ (T - s)
    rw [intervalIntegral_integral_swap (f := fun (v : ℝ) (z : E) => Λ s z * K.apply v ψ z)
      (by rwa [Set.uIoc_of_le hh.le])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hgen hh z, intervalIntegral.integral_const_mul]
  have h3 : ∫ v in (0 : ℝ)..(T - s), ∫ z, Λ s z * K.apply v ψ z ∂μ =
      ∫ v in (0 : ℝ)..(T - s), ∫ y, Λ (s + v) y * ψ y ∂μ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Set.uIoc_of_le hh.le] at hv
    exact (hΛ.integral_apply_mul hK hs' hψ hv.1).symm
  rw [h1, h2, h3, intervalIntegral.integral_comp_add_left (fun u => ∫ y, Λ u y * ψ y ∂μ) s]
  simp [hTs]

end RegularityStructures.RegularisingSemigroup

end
