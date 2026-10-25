/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Main
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit

/-!
# The pairing bound with a free time `T` and a free radius `R`

`abs_pairing_le_of_time`: for `Λ` of local order `γ` at `x₀`, `φ`, `ψ` supported in the ball of
radius `R` about `x₀`, `ψ = Lφ`, and any `T ∈ (0, 1]`,

  `|⟨Λ, φ⟩| ≤ C (∑_a T^{a/ℓ} R^{γ-a}) B₀ + incrBound A γ R (C B₁' R^{-ℓ}) T`.

Unlike `abs_pairing_le` this does not tie `T` to the radius (`T = R^ℓ`), so it applies to test
functions of radius `R > 1` (take `T = 1`) and to test functions centred at a point `y ≠ x₀`
(take `R = λ + d(y, x₀)` and `T = λ^ℓ`), as needed for the Taylor-remainder estimates
[Hai14, Lemma 5.18, Lemma 5.19].
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem LocalData.exists_tendsto_abs_le_of_time [SFinite μ] (hK : K.IsSymmetric)
    (hd : K.IsMetricScale) (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalData Λ x₀ γ A C) (hA : ∀ a ∈ A, -K.order < a)
    {φ ψ : E → ℝ} {R B₀ B₁ T : ℝ} (hR : 0 < R) (hB₁ : 0 ≤ B₁) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀)
    (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * R ^ (-K.order)) (hgen : K.IsGeneratorPair φ ψ)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * (∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a)) * B₀ +
        K.incrBound A γ R (C * (B₁ * R ^ (-K.order))) T := by
  obtain ⟨L, hL⟩ := hΛ.exists_tendsto_integral hK hd hJ hA hR hB₁ hφ hψ hgen hψ1
  refine ⟨L, hL, ?_⟩
  have hTm : T ∈ Set.Ioc (0 : ℝ) 1 := ⟨hT, hT1⟩
  have h1 := hΛ.abs_integral_mul_le hTm hφ
  have hS : 0 ≤ C * ∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a) :=
    mul_nonneg hΛ.nonneg (Finset.sum_nonneg fun a _ =>
      mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hR.le _))
  have hb : ∀ s ∈ Set.Ioo 0 T, |∫ y, Λ s y * φ y ∂μ| ≤
      C * (∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a)) * B₀ +
        K.incrBound A γ R (C * (B₁ * R ^ (-K.order))) T := by
    intro s hs
    have h2 := hΛ.abs_integral_sub_le hK hd hJ hA hR hB₁ hφ hψ hgen hψ1 hs.1 hs.2 hT1
    calc _ = |(∫ y, Λ T y * φ y ∂μ) - ((∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ)| := by
          congr 1; ring
      _ ≤ |∫ y, Λ T y * φ y ∂μ| + |(∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ| :=
          abs_sub _ _
      _ ≤ _ := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hφ1 hS)) h2
  exact le_of_tendsto hL.abs (Filter.mem_of_superset (Ioo_mem_nhdsGT hT) hb)

theorem abs_pairing_le_of_time [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalData Λ x₀ γ A C) (hA : ∀ a ∈ A, -K.order < a)
    {φ ψ : E → ℝ} {R B₀ B₁ T : ℝ} (hR : 0 < R) (hB₁ : 0 ≤ B₁) (hφ : K.IsSupported φ x₀ R)
    (hψ : K.IsSupported ψ x₀ R) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀)
    (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * R ^ (-K.order)) (hgen : K.IsGeneratorPair φ ψ)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    |K.pairing Λ φ| ≤ C * (∑ a ∈ A, T ^ (a / K.order) * R ^ (γ - a)) * B₀ +
        K.incrBound A γ R (C * (B₁ * R ^ (-K.order))) T := by
  obtain ⟨L, hL, hb⟩ := hΛ.exists_tendsto_abs_le_of_time hK hd hJ hA hR hB₁ hφ hψ hφ1 hψ1 hgen hT hT1
  rwa [K.pairing_eq_of_tendsto hL]

end RegularityStructures.RegularisingSemigroup

end
