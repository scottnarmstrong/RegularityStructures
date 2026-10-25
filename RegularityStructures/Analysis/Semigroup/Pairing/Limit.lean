/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Main
public import RegularityStructures.Analysis.Semigroup.Pairing.Tendsto
public import RegularityStructures.Analysis.Semigroup.Pairing.TendstoIntegral

/-!
# The pairing with a test function

For a `Q`-distribution of local order, the limit `⟨Λ, φ⟩ = lim_{s↓0} ∫ Λ_s φ` exists and satisfies the
test-function bound (`tendsto_integral_pairing`, `abs_pairing_le`).
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem LocalData.abs_integral_order_le {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalData Λ x₀ γ A C) {φ : E → ℝ} {lam B₀ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hφ : K.IsSupported φ x₀ lam) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) :
    |∫ y, Λ (lam ^ K.order) y * φ y ∂μ| ≤ C * B₀ * A.card * lam ^ γ := by
  have hℓ := K.order_pos
  have hT : lam ^ K.order ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hlam _, Real.rpow_le_one hlam.le hlam1 hℓ.le⟩
  refine (hΛ.abs_integral_mul_le hT hφ).trans ?_
  have e : ∀ a ∈ A, (lam ^ K.order) ^ (a / K.order) * lam ^ (γ - a) = lam ^ γ := by
    intro a _
    rw [← Real.rpow_mul hlam.le, mul_div_cancel₀ _ hℓ.ne', ← Real.rpow_add hlam]
    congr 1; ring
  rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
  have hnn : 0 ≤ C * (A.card * lam ^ γ) :=
    mul_nonneg hΛ.nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hlam.le _))
  calc _ ≤ (C * (A.card * lam ^ γ)) * B₀ := mul_le_mul_of_nonneg_left hφ1 hnn
    _ = _ := by ring

/-- Existence of the pairing and the test-function bound at the level of `LocalData`. -/
theorem LocalData.exists_tendsto_abs_le [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalData Λ x₀ γ A C) (hA : ∀ a ∈ A, -K.order < a) {φ ψ : E → ℝ}
    {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hφ : K.IsSupported φ x₀ lam)
    (hψ : K.IsSupported ψ x₀ lam) (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀)
    (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order)) (hgen : K.IsGeneratorPair φ ψ) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  have hℓ := K.order_pos
  have hB₀ : 0 ≤ B₀ := (integral_nonneg fun _ => abs_nonneg _).trans hφ1
  have hB₁ : 0 ≤ B₁ := by
    have h0 : 0 ≤ B₁ * lam ^ (-K.order) := (integral_nonneg fun _ => abs_nonneg _).trans hψ1
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hlam _)).1 h0
  obtain ⟨L, hL⟩ := hΛ.exists_tendsto_integral hK hd hJ hA hlam hB₁ hφ hψ hgen hψ1
  refine ⟨L, hL, ?_⟩
  set T := lam ^ K.order with hTdef
  have hT0 : 0 < T := Real.rpow_pos_of_pos hlam _
  have hT1 : T ≤ 1 := Real.rpow_le_one hlam.le hlam1 hℓ.le
  have hbd : ∀ s ∈ Set.Ioo 0 T, |∫ y, Λ s y * φ y ∂μ| ≤
      C * B₀ * A.card * lam ^ γ + C * B₁ * lam ^ γ * ∑ a ∈ A, K.order / (a + K.order) := by
    intro s hs
    have h1 := hΛ.abs_integral_order_le hlam hlam1 hφ hφ1
    have h2 := hΛ.abs_integral_sub_le hK hd hJ hA hlam hB₁ hφ hψ hgen hψ1 hs.1 hs.2 hT1
    rw [incrBound_pow_order hA hlam] at h2
    calc _ = |(∫ y, Λ T y * φ y ∂μ) - ((∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ)| := by
          congr 1; ring
      _ ≤ |∫ y, Λ T y * φ y ∂μ| + |(∫ y, Λ T y * φ y ∂μ) - ∫ y, Λ s y * φ y ∂μ| :=
          abs_sub _ _
      _ ≤ _ := by
          exact add_le_add h1 h2
  have hlim : |L| ≤ C * B₀ * A.card * lam ^ γ +
      C * B₁ * lam ^ γ * ∑ a ∈ A, K.order / (a + K.order) :=
    le_of_tendsto hL.abs (Filter.mem_of_superset (Ioo_mem_nhdsGT hT0) hbd)
  refine hlim.trans ?_
  have hS : 0 ≤ ∑ a ∈ A, K.order / (a + K.order) :=
    Finset.sum_nonneg fun a ha => div_nonneg hℓ.le (by linarith [hA a ha])
  have hpc : K.pairingConst A = A.card + ∑ a ∈ A, K.order / (a + K.order) := by
    simp [pairingConst, Finset.sum_add_distrib]
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

theorem tendsto_integral_pairing [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hloc : K.IsLocalOrder Λ x₀ γ A C)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 (K.pairing Λ φ)) := by
  obtain ⟨L, hL, -⟩ := (LocalData.mk hΛ hΛm hC (fun a ha => (hA a ha).2) hloc).exists_tendsto_abs_le
    hK hd hJ (fun a ha => (hA a ha).1) hlam hlam1 ⟨hφm, hφi, hφs⟩ ⟨hψm, hψi, hψs⟩ hφ1 hψ1 hgen
  rwa [K.pairing_eq_of_tendsto hL]

theorem abs_pairing_le [SFinite μ] (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {x₀ : E} {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -K.order < a ∧ a ≤ γ) {C : ℝ} (hC : 0 ≤ C) (hloc : K.IsLocalOrder Λ x₀ γ A C)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    |K.pairing Λ φ| ≤ C * K.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  obtain ⟨L, hL, hb⟩ := (LocalData.mk hΛ hΛm hC (fun a ha => (hA a ha).2) hloc).exists_tendsto_abs_le
    hK hd hJ (fun a ha => (hA a ha).1) hlam hlam1 ⟨hφm, hφi, hφs⟩ ⟨hψm, hψi, hψs⟩ hφ1 hψ1 hgen
  rwa [K.pairing_eq_of_tendsto hL]

end RegularityStructures.RegularisingSemigroup

end
