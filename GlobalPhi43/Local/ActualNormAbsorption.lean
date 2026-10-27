/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CausalNormEmbedding
public import GlobalPhi43.Local.WeightedAffineMonotonicity
public import GlobalPhi43.Local.CausalAbsorption
public import GlobalPhi43.Local.RadiusSourceSize
public import GlobalPhi43.Local.TwoSidedRadiusNorm

/-! A finite norm recurrence implies the two-sided bound, assuming the
corresponding PDE recurrence. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal ContDiff BigOperators

/-- All constants precede the germ and data. Finiteness and the embedding
are derived from local smoothness; the sole remaining analytic input is
the recurrence for the actual weighted affine-error supremum. -/
theorem actual_norm_absorption {I : Type*} (A : Finset I) (β : I → ℝ)
    {θ η γ a b : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 16)
    (hθ : θ ≤ 1) (hηθ : 4 * η ≤ θ) (hγ : 1 < γ) (hγ₂ : γ ≤ 2) (hβγ : ∀ i ∈ A, β i ≤ γ)
    (ha : a ≤ 1 / 2) (hb : b * campanatoFactor γ ≤ 1 / 4) :
    ∃ C > 0, ∀ (U : GermPoint → ℝ) (r d₀ P M : ℝ), 0 ≤ r → 0 ≤ P → 0 ≤ M →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      (∀ x ∈ sourceCylinder r, U (x, x) = 0) →
      ((weightedPastAffineError U r d₀ θ γ).toReal ≤
        a * (weightedPastAffineError U r d₀ θ γ).toReal + P +
        b * (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ y ∈ sourceCylinder r, y ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall y (d / 4) →
        d ^ γ * |U (x, z) - U (x, y) - U (y, z)| ≤
          M * ∑ i ∈ A, pdist x y ^ β i * pdist y z ^ (γ - β i)) →
      weightedRadiusAffineSeminorm U r d₀ γ ≤
        ENNReal.ofReal (C * ((radiusSourceUSup U r d₀).toReal + P + M)) := by
  obtain ⟨C, hC, hsided⟩ := two_sided_radius_norm_of_causal_bound A β hη hηsmall hγ.le hβγ
  have hH := (campanatoFactor_pos hγ).le
  refine ⟨C * (1 + 4 * campanatoFactor γ), by positivity, ?_⟩
  intro U r d₀ P M hr hP hM hU hdiag hrec hthree
  have hBfinite := radiusSourceUSup_ne_top U (d₀ := d₀) hr hU
  have hQfinite := smallPastRemainderSeminorm_ne_top U (d₀ := d₀) hr hη hηsmall
    (by linarith) hγ₂ hU hdiag
  have hembed := smallPastSeminorm_toReal_le_campanato U (d₀ := d₀) hr hη hηsmall hγ hγ₂ hU hdiag
  have hFfinite := weightedPastAffineError_ne_top U (d₀ := d₀) hr hθ (by linarith) hγ₂ hU
  have hFmono := ENNReal.toReal_mono hFfinite (weightedPastAffineError_mono_radius U (r := r)
    (d₀ := d₀) (γ := γ) hηθ)
  have hembed' := hembed.trans (mul_le_mul_of_nonneg_left hFmono hH)
  have hQ := two_stage_causal_absorption ENNReal.toReal_nonneg ENNReal.toReal_nonneg hH ha hb hrec hembed'
  have hout := hsided (fun x y => U (x, y)) (diagonalSpatialCoefficient U)
    r d₀ (radiusSourceUSup U r d₀).toReal
    (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal M
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hM
    (fun d hd x hx y hy hxy => radiusSourceUSup_bound U hBfinite hd hx hy hxy)
    (fun d hd x hx y hy => smallPastRemainderSeminorm_bound U _ hQfinite hd hx hy)
    hthree
  apply hout.trans
  apply ENNReal.ofReal_le_ofReal
  have hB : 0 ≤ (radiusSourceUSup U r d₀).toReal := ENNReal.toReal_nonneg
  have hbudget : (radiusSourceUSup U r d₀).toReal +
      (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal + M ≤
      (1 + 4 * campanatoFactor γ) * ((radiusSourceUSup U r d₀).toReal + P + M) := by
    nlinarith [mul_nonneg hH hB, mul_nonneg hH hM]
  nlinarith [mul_le_mul_of_nonneg_left hbudget hC.le]

end GlobalPhi43.Local
