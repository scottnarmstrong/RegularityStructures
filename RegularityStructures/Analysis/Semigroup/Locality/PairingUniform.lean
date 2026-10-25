/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Locality.Pairing

/-!
# Uniform bound for the regularised pairings of a distribution of local order on a ball

Refinement of `exists_tendsto_abs_le_of_local`: besides the limit `L = ⟨Λ, φ⟩` and its bound, the
regularised pairings `∫ Λ_s φ`, `0 < s < λ^ℓ`, obey the same bound
`C · pairingConst A · (B₀ + B₁) · λ^γ` uniformly in `s`
(`exists_tendsto_abs_le_uniform_of_local`).  This is the quantitative form needed to
differentiate the regularised pairing in the centre of the test function.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 3.10, (3.3).
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

/-- The limit of the regularised pairings, its bound, and the uniform bound for `0 < s < λ^ℓ`. -/
theorem LocalBall.exists_tendsto_abs_le_uniform [SFinite μ] (hK : K.IsSymmetric)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) (hA : ∀ a ∈ A, -K.order < a) {φ ψ : E → ℝ}
    {B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hφ : K.IsSupported φ x₀ lam)
    (hψ : K.IsSupported ψ x₀ lam) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀)
    (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order)) (hgen : K.IsGeneratorPair φ ψ) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ ∧
      ∀ s ∈ Set.Ioo 0 (lam ^ K.order),
        |∫ y, Λ s y * φ y ∂μ| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  have hℓ := K.order_pos
  have hB₀ : 0 ≤ B₀ := (integral_nonneg fun _ => abs_nonneg _).trans hφ1
  have hB₁ : 0 ≤ B₁ := by
    have h0 : 0 ≤ B₁ * lam ^ (-K.order) := (integral_nonneg fun _ => abs_nonneg _).trans hψ1
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hlam _)).1 h0
  obtain ⟨L, hL⟩ := hΛ.exists_tendsto_integral hK hJ hA hlam hB₁ hφ hψ hgen hψ1
  set T := lam ^ K.order with hTdef
  have hT0 : 0 < T := Real.rpow_pos_of_pos hlam _
  have hT1 : T ≤ 1 := Real.rpow_le_one hlam.le hlam1 hℓ.le
  have hbd : ∀ s ∈ Set.Ioo 0 T, |∫ y, Λ s y * φ y ∂μ| ≤
      C * B₀ * A.card * lam ^ γ + C * B₁ * lam ^ γ * ∑ a ∈ A, K.order / (a + K.order) := by
    intro s hs
    have h1 := hΛ.abs_integral_order_le hlam hlam1 hφ hφ1
    have h2 := hΛ.abs_integral_sub_le hK hJ hA hlam hB₁ hφ hψ hgen hψ1 hs.1 hs.2 hT1
    rw [incrBound_pow_order hA hlam] at h2
    calc _ = |(∫ y, Λ T y * φ y ∂μ) - ((∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ)| := by
          congr 1; ring
      _ ≤ |∫ y, Λ T y * φ y ∂μ| + |(∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ| :=
          abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have hS : 0 ≤ ∑ a ∈ A, K.order / (a + K.order) :=
    Finset.sum_nonneg fun a ha => div_nonneg hℓ.le (by linarith [hA a ha])
  have hpc : K.pairingConst A = A.card + ∑ a ∈ A, K.order / (a + K.order) := by
    simp [pairingConst, Finset.sum_add_distrib]
  have hfin : C * B₀ * A.card * lam ^ γ + C * B₁ * lam ^ γ * ∑ a ∈ A, K.order / (a + K.order) ≤
      C * K.pairingConst A * (B₀ + B₁) * lam ^ γ := by
    rw [hpc]
    have hX : 0 ≤ C * lam ^ γ := mul_nonneg hΛ.nonneg (Real.rpow_nonneg hlam.le _)
    have hc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have key : B₀ * A.card + B₁ * ∑ a ∈ A, K.order / (a + K.order) ≤
        (A.card + ∑ a ∈ A, K.order / (a + K.order)) * (B₀ + B₁) := by
      nlinarith [mul_nonneg hB₀ hS, mul_nonneg hB₁ hc]
    calc _ = (C * lam ^ γ) * (B₀ * A.card + B₁ * ∑ a ∈ A, K.order / (a + K.order)) := by ring
      _ ≤ (C * lam ^ γ) * ((A.card + ∑ a ∈ A, K.order / (a + K.order)) * (B₀ + B₁)) :=
          mul_le_mul_of_nonneg_left key hX
      _ = _ := by ring
  refine ⟨L, hL, ?_, fun s hs => (hbd s hs).trans hfin⟩
  exact (le_of_tendsto hL.abs (Filter.mem_of_superset (Ioo_mem_nhdsGT hT0) hbd)).trans hfin

/-- Uniform version of `exists_tendsto_abs_le_of_local`. -/
theorem exists_tendsto_abs_le_uniform_of_local [SFinite μ] (hK : K.IsSymmetric)
    (hd : K.IsMetricScale) (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ q C' β R : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hq : 0 ≤ q)
    (hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ R →
      |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a))
    (hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
      |Λ u y| ≤ C' * u ^ (β / K.order) * (1 + K.scaleDist y x₀) ^ q)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamR : lam ≤ R)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ ∧
      ∀ s ∈ Set.Ioo 0 (lam ^ K.order),
        |∫ y, Λ s y * φ y ∂μ| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ :=
  (LocalBall.of_local hd hΛ hΛm hC hC' hq (fun a ha => (hA a ha).2) hloc hcrude hlam.le
    hlamR).exists_tendsto_abs_le_uniform hK hJ (fun a ha => (hA a ha).1) hlam hlam1
    ⟨hφm, hφi, hφs⟩ ⟨hψm, hψi, hψs⟩ hφ1 hψ1 hgen

end RegularityStructures.RegularisingSemigroup

end
