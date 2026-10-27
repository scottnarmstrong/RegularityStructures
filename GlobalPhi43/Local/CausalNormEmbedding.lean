/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.WeightedAffineExtraction
public import GlobalPhi43.Local.SmallPastSeminorm
public import GlobalPhi43.Local.SectionDerivative
public import GlobalPhi43.Local.CampanatoInfimum

/-! The actual Q_epsilon is controlled by the actual weighted affine-error
quantity. All finiteness facts come from standing local smoothness. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal ContDiff

theorem campanatoFactor_pos {γ : ℝ} (hγ : 1 < γ) : 0 < campanatoFactor γ := by
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ (γ - 1) := by
    have hh := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : 0 < γ - 1)
    linarith
  unfold campanatoFactor
  positivity

/-- Passage from the weighted affine infima to the weighted
small-past remainders with the prescribed diagonal spatial coefficient. -/
theorem smallPastSeminorm_le_campanato (U : GermPoint → ℝ)
    {r d₀ η γ : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hηsmall : η ≤ 1 / 16)
    (hγ : 1 < γ) (hγ₂ : γ ≤ 2)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0) :
    smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ ≤
      ENNReal.ofReal (campanatoFactor γ * (weightedPastAffineError U r d₀ (4 * η) γ).toReal) := by
  have hF := weightedPastAffineError_ne_top U (d₀ := d₀) hr (by linarith : 4 * η ≤ 1) (by linarith) hγ₂ hU
  obtain ⟨O, hO, hKO, hs⟩ := hU
  apply smallPastRemainderSeminorm_le
  intro d hd x hx y hy
  have hxD := cylinderInterior_mem_domain hd.1.le hx
  have hDU : DifferentiableAt ℝ U (x, x) :=
    (hs.contDiffAt (hO.mem_nhds (hKO ⟨subset_closure hxD, subset_closure hxD⟩))).differentiableAt (by simp)
  have hdpos : 0 < d := hd.1
  have hR : 0 < 4 * η * d := by positivity
  have herror (n : ℕ) : pastAffineError (fun z => U (x, z)) x ((4 * η * d) * (1 / 2 : ℝ) ^ n) ≤
      ENNReal.ofReal (((weightedPastAffineError U r d₀ (4 * η) γ).toReal / d ^ γ) *
        ((4 * η * d) * (1 / 2 : ℝ) ^ n) ^ γ) := by
    apply weightedPastAffineError_bound_toReal U hF hd hx
    constructor
    · positivity
    · exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hy' : y ∈ pastBall x (4 * η * d) := ⟨by nlinarith [hy.1], hy.2⟩
  have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ hy.2)
  have hρ := pdist_pos_of_ne hne
  have hb := causal_holder_of_affine_error (fun z => U (x, z)) x (sectionSecondDerivative U (x, x))
    (section_hasFDerivAt U x x hDU) (hdiag x hxD) hR hγ
    (div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hd.1.le γ)) herror hy' hρ
  rw [affineRemainder, diagonalCoefficient_eq_second_derivative U x hDU]
  rw [Real.div_rpow hρ.le hd.1.le]
  convert hb using 1; ring

/-- The same exact finite real quantities satisfy the embedding
inequality used in the subsequent two-stage absorption. -/
theorem smallPastSeminorm_toReal_le_campanato (U : GermPoint → ℝ)
    {r d₀ η γ : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hηsmall : η ≤ 1 / 16)
    (hγ : 1 < γ) (hγ₂ : γ ≤ 2)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0) :
    (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal ≤
      campanatoFactor γ * (weightedPastAffineError U r d₀ (4 * η) γ).toReal := by
  have hh := smallPastSeminorm_le_campanato U (d₀ := d₀) hr hη hηsmall hγ hγ₂ hU hdiag
  have hrhs : 0 ≤ campanatoFactor γ * (weightedPastAffineError U r d₀ (4 * η) γ).toReal :=
    mul_nonneg (campanatoFactor_pos hγ).le ENNReal.toReal_nonneg
  simpa only [ENNReal.toReal_ofReal hrhs] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hh

end GlobalPhi43.Local
