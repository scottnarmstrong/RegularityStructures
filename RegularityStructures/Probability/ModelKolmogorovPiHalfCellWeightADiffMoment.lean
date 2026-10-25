/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADiffPath
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightAMoment

/-!
# The moment of the random part of the difference weight (A3)

`exists_piHalfCellDiffRandPartA_moment_le`: for `s ∈ (0, 1]` and `2 p ≤ q`,
`∫⁻ ω, R₁₂(ω)^p ≤ (K max(1,C) (C ε^θ) s^((deg k + κbar)/4))^p`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pointwise moment of one summand of the difference. -/
theorem piHalf_diffTerm_pointwise_moment {𝒯 : RegularityStructure ι}
    {γ κbar θ C ε : ℝ} {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hH₁ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₁ C)
    (hH₂ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₂ C)
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) {k : ι} (hkγ : 𝒯.deg k < γ) {p : ℕ} (hp : 1 ≤ p)
    (hpq : 2 * p ≤ q) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (x₀ w : ParabolicSpace)
    (hmPi₁ : ∀ j, Measurable fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w)
    (hmPi₂ : ∀ j, Measurable fun ω => (Z₂ ω).regPi w (Pi.single j 1) s w)
    (hmGam₁ : ∀ j, Measurable fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j)
    (hmGam₂ : ∀ j, Measurable fun ω => (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j)
    {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) (b : Bool) :
    ∫⁻ ω, piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, b) w ^ p ∂P ≤
      ENNReal.ofReal (max 1 C * (C * ε ^ θ) * s ^ piHalfRandBetaA 𝒯 κbar Dπ j *
        parabolicNorm (x₀ - w) ^ piHalfRandAlphaA 𝒯 κbar DΓ k j) ^ p := by
  have hd := Real.rpow_nonneg (parabolicNorm_nonneg (x₀ - w)) (piHalfRandAlphaA 𝒯 κbar DΓ k j)
  have hsb := Real.rpow_nonneg hs.1.le (piHalfRandBetaA 𝒯 κbar Dπ j)
  have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hCd : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  cases b
  · -- `(Γ¹ - Γ²) Π²`
    have hF := piHalf_factorBound_gammaDiff hD hkγ hjk hC hε x₀ w
    have hG := (piHalf_factorBound_pi hH₂ hkγ hjk hs w).mono
      (le_trans (le_of_eq rfl) (mul_le_mul_of_nonneg_right (le_max_right 1 C) hsb))
    have h := piHalf_lintegral_mul_pow_le_of_factorBound hp hpq
      ((hmGam₁ j).sub (hmGam₂ j)) (hmPi₂ j)
      (mul_nonneg hCd hd) hF hG
    refine h.trans (le_of_eq ?_)
    congr 2
    ring
  · -- `Γ¹ (Π¹ - Π²)`
    have hF := (piHalf_factorBound_gamma hH₁ hkγ hjk x₀ w)
    have hG := piHalf_factorBound_piDiff hD hkγ hjk hs w
    have h := piHalf_lintegral_mul_pow_le_of_factorBound hp hpq
      (hmGam₁ j) ((hmPi₁ j).sub (hmPi₂ j)) (mul_nonneg hCm hd) hF hG
    refine h.trans (le_of_eq ?_)
    congr 2
    ring

theorem measurable_piHalfCellDiffTermA_omega {𝒯 : RegularityStructure ι} {Ω : Type*}
    [MeasurableSpace Ω] {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup} {s : ℝ}
    {x₀ w : ParabolicSpace} {k : ι}
    (hmPi₁ : ∀ j, Measurable fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w)
    (hmPi₂ : ∀ j, Measurable fun ω => (Z₂ ω).regPi w (Pi.single j 1) s w)
    (hmGam₁ : ∀ j, Measurable fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j)
    (hmGam₂ : ∀ j, Measurable fun ω => (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j) (jb : ι × Bool) :
    Measurable fun ω => piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) jb w := by
  obtain ⟨j, b⟩ := jb
  cases b
  · exact ((hmGam₁ j).sub (hmGam₂ j)).enorm.mul (hmPi₂ j).enorm
  · exact (hmGam₁ j).enorm.mul ((hmPi₁ j).sub (hmPi₂ j)).enorm

end RegularityStructures

end
