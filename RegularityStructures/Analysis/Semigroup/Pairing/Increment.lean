/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Fubini
public import RegularityStructures.Analysis.Semigroup.Pairing.FubiniBound

/-!
# The increment identity `G(T) - G(s) = ∫_s^T ∫ Λ_u ψ du`

For `ψ = Lφ` (`IsGeneratorPair φ ψ`) and a distribution `Λ` of local order `γ`, the function
`G(u) = ∫ Λ_u φ` satisfies `G(T) - G(s) = ∫_s^T (∫ Λ_u ψ) du`
(`LocalData.integral_sub_integral_eq_integral`): by the symmetry of the kernel,
`G(s + h) = ∫ Λ_s Q_h φ`, and `Q_h φ - φ = ∫_0^h Q_v ψ dv`; then Fubini in `v`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

/-- [Hai14, proof of Theorem 3.10]: `∫ Λ_T φ - ∫ Λ_s φ = ∫_s^T ∫ Λ_u ψ du` for `0 < s < T ≤ 1`. -/
theorem LocalData.integral_sub_integral_eq_integral [SFinite μ] (hK : K.IsSymmetric)
    (hd : K.IsMetricScale) (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalData Λ x₀ γ A C) {φ ψ : E → ℝ} {lam : ℝ}
    (hφ : K.IsSupported φ x₀ lam) (hψ : K.IsSupported ψ x₀ lam) (hgen : K.IsGeneratorPair φ ψ)
    {s T : ℝ} (hs : 0 < s) (hsT : s < T) (hT : T ≤ 1) :
    ∫ y, Λ T y * φ y ∂μ - ∫ y, Λ s y * φ y ∂μ = ∫ u in s..T, ∫ y, Λ u y * ψ y ∂μ := by
  have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs, hsT.le.trans hT⟩
  have hh : 0 < T - s := sub_pos.2 hsT
  have hTs : s + (T - s) = T := by ring
  have h1 : ∫ y, Λ T y * φ y ∂μ - ∫ y, Λ s y * φ y ∂μ =
      ∫ z, Λ s z * (K.apply (T - s) φ z - φ z) ∂μ := by
    have := hΛ.integral_apply_mul hK hd hs' hφ hh
    rw [hTs] at this
    rw [this, ← integral_sub (hΛ.integrable_mul_apply hK hd hs' hφ hh) (hΛ.integrable_mul hs' hφ)]
    simp only [mul_sub]
  have h2 : ∫ z, Λ s z * (K.apply (T - s) φ z - φ z) ∂μ =
      ∫ v in (0 : ℝ)..(T - s), ∫ z, Λ s z * K.apply v ψ z ∂μ := by
    have hint := hΛ.integrable_uncurry_apply hK hd hJ hs' hψ (T - s)
    rw [intervalIntegral_integral_swap (f := fun (v : ℝ) (z : E) => Λ s z * K.apply v ψ z)
      (by rwa [Set.uIoc_of_le hh.le])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hgen hh z, intervalIntegral.integral_const_mul]
  have h3 : ∫ v in (0 : ℝ)..(T - s), ∫ z, Λ s z * K.apply v ψ z ∂μ =
      ∫ v in (0 : ℝ)..(T - s), ∫ y, Λ (s + v) y * ψ y ∂μ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Set.uIoc_of_le hh.le] at hv
    exact (hΛ.integral_apply_mul hK hd hs' hψ hv.1).symm
  rw [h1, h2, h3, intervalIntegral.integral_comp_add_left (fun u => ∫ y, Λ u y * ψ y ∂μ) s]
  simp [hTs]

end RegularityStructures.RegularisingSemigroup

end
