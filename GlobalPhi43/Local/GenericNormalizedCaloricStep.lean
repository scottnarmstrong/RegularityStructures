/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SourceLocalCaloricSupplier
public import GlobalPhi43.Local.SourceSmoothingError
public import GlobalPhi43.Local.AffineErrorComparison
public import GlobalPhi43.Local.SourceHeatSupremum
public import GlobalPhi43.MW20.NormalizedAffineComparison
public import GlobalPhi43.MW20.RadiusSmoothingNormalization
public import GlobalPhi43.MW20.OnePointForcingNormalization

/-! Normalized caloric estimates at the original scales. The one-point
forcing and three-point bounds are assumed; caloric regularity, commutation
and finiteness are derived. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_generic_normalized_caloric_step {I J : Type*}
    (A : Finset I) (α : I → ℝ) (B : Finset J) (β : J → ℝ)
    {γ : ℝ} (hγ : 1 < γ) (hγ₂ : γ ≤ 2)
    (hβ : ∀ j ∈ B, 0 ≤ β j) (hβγ : ∀ j ∈ B, β j ≤ γ) :
    ∃ C > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
      (r d₀ d ε L M₁ M₂ H : ℝ) (hε : 0 < ε) (hL : 0 < L),
      0 ≤ r → d ∈ Ioc (0 : ℝ) d₀ → ε ≤ 1 / 4 → L ≤ d / 8 →
      0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ H →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      (∀ x ∈ sourceCylinder r, U (x, x) = 0) →
      ∀ x ∈ cylinderInterior r d,
      (∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
        d ^ γ * |U (x, z) - U (x, b) - U (b, z)| ≤
          M₂ * ∑ j ∈ B, pdist x b ^ β j * pdist b z ^ (γ - β j)) →
      (ENNReal.ofReal (d ^ γ * L ^ (-γ)) * pastAffineError (fun y => U (x, y)) x L ≤
        ENNReal.ofReal H) →
      let T := ε ^ 2 * L
      let μ := infiniteKernelMeasure Φ hΦ T (mul_pos (sq_pos_of_pos hε) hL)
      (d ^ γ * T ^ 2 * (localScalarSup (fun y => ∫ w,
        sourceHeat (fun z => U (x, z)) (y + w) ∂μ) (pastBall x L)).toReal ≤
          M₁ * ∑ i ∈ A, T ^ α i * L ^ (γ - α i)) →
      ENNReal.ofReal (d ^ γ * (ε * L) ^ (-γ)) *
        pastAffineError (fun y => U (x, y)) x (ε * L) ≤
        ENNReal.ofReal (C * ε ^ (2 - γ) * H +
          C * M₁ * (∑ i ∈ A, ε ^ (2 * α i - 4 - γ)) +
          M₂ * ((∑ j ∈ B, ε ^ (γ - β j)) + C * (∑ j ∈ B, ε ^ (2 + γ - 2 * β j))) +
          (8 / 7 : ℝ) ^ γ * (ε ^ γ + C * ε ^ (2 + γ)) *
            (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ (ε / 32) γ).toReal) := by
  obtain ⟨C, hC, hcal⟩ := exists_source_local_caloric_supplier
  refine ⟨C, hC, ?_⟩
  intro Φ hΦ U r d₀ d ε L M₁ M₂ H hε hL hr hd hεsmall hLd hM₁ hM₂ hH hU hdiag x hx hthree hlarge
  dsimp only
  intro hP2
  have hd1 : d < 1 := by nlinarith [hx.1, hx.2.1, sq_nonneg r, hd.1]
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hTL : ε ^ 2 * L ≤ L := mul_le_of_le_one_left hL.le hεsq
  have hT1 : ε ^ 2 * L ≤ 1 := by linarith
  have hLT : L + ε ^ 2 * L ≤ d := by linarith
  let μ := infiniteKernelMeasure Φ hΦ (ε ^ 2 * L) (mul_pos (sq_pos_of_pos hε) hL)
  let g := pastSmooth μ (fun y => U (x, y))
  let Q := (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ (ε / 32) γ).toReal
  have heq := source_section_heat_supremum_eq Φ hΦ U hr (mul_pos (sq_pos_of_pos hε) hL) hT1 hL.le hLT hU hx
  rw [← heq] at hP2
  have hP2g : d ^ γ * (ε ^ 2 * L) ^ 2 *
      (localScalarSup (sourceHeat g) (pastBall x L)).toReal ≤
        M₁ * ∑ i ∈ A, (ε ^ 2 * L) ^ α i * L ^ (γ - α i) := by
    simpa only [g, μ, pastSmooth] using! hP2
  have hforce : (d ^ γ * (ε * L) ^ (-γ)) * L ^ 2 *
      (localScalarSup (sourceHeat g) (pastBall x L)).toReal ≤
        M₁ * ∑ i ∈ A, ε ^ (2 * α i - 4 - γ) := by
    have hh : (ε ^ 2 * L) ^ 2 *
        (d ^ γ * (localScalarSup (sourceHeat g) (pastBall x L)).toReal) ≤
        M₁ * ∑ i ∈ A, (ε ^ 2 * L) ^ α i * L ^ (γ - α i) := by
      convert hP2g using 1
      ring
    convert one_point_forcing_normalization A α hε hL hh using 1
    ring
  have hnear : ∀ y ∈ pastBall x (ε * L),
      (d ^ γ * (ε * L) ^ (-γ)) * |U (x, y) - g y| ≤
        M₂ * (∑ j ∈ B, ε ^ (γ - β j)) + (8 / 7 : ℝ) ^ γ * Q * ε ^ γ := by
    intro y hy
    have hh := source_smoothing_error B β Φ hΦ U hr hd hε hεsmall hL hLd
      (mul_pos hε hL).le (mul_le_of_le_one_left hL.le (by linarith : ε ≤ 1))
      hγ hγ₂ hM₂ hβ hβγ hU hdiag hx hy hthree
    rw [← integral_infiniteKernelMeasure Φ hΦ (mul_pos (sq_pos_of_pos hε) hL) hT1] at hh
    have hn := radius_smoothing_normalization_near B β hd.1 hε hL hh
    simpa only [g, μ, pastSmooth, abs_sub_comm] using hn
  have hfar : ∀ y ∈ pastBall x L,
      ((d ^ γ * (ε * L) ^ (-γ)) * ((ε * L) / L) ^ 2) * |g y - U (x, y)| ≤
        M₂ * (∑ j ∈ B, ε ^ (2 + γ - 2 * β j)) + (8 / 7 : ℝ) ^ γ * Q * ε ^ (2 + γ) := by
    intro y hy
    have hh := source_smoothing_error B β Φ hΦ U hr hd hε hεsmall hL hLd
      hL.le le_rfl hγ hγ₂ hM₂ hβ hβγ hU hdiag hx hy hthree
    rw [← integral_infiniteKernelMeasure Φ hΦ (mul_pos (sq_pos_of_pos hε) hL) hT1] at hh
    have hf := radius_smoothing_normalization_far B β hd.1 hε hL hh
    simpa only [g, μ, pastSmooth, Q, mul_assoc] using! hf
  have hheat := hcal Φ hΦ U r d ε L hε hL hr (by linarith) hT1 hLT hU x hx
  have hout := normalized_affine_comparison_step (fun y => U (x, y)) g x hd.1 hε hL
    hC.le hH (by positivity) (by dsimp [Q]; positivity) (by dsimp [Q]; positivity)
    hheat hlarge hnear hfar hforce
  apply hout.trans
  apply ENNReal.ofReal_le_ofReal
  dsimp only [Q]
  ring_nf
  exact le_rfl

end GlobalPhi43.Local
