/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyRand

/-!
# Moment of the concrete random part, difference version
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moment bound for the concrete random part of the difference. -/
theorem lintegral_piHalfCellDiffRand_pow_le (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (T : Set ParabolicSpace) (κ C ε θ c₀ : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (KR : ι → ℝ) (hKR : ∀ k, 0 ≤ KR k) (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C * ε ^ θ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (j : ℕ) (i : ι)
    (c : ℕ)
    (hmeas : ∀ k, AEMeasurable (fun ω => piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j)
      (piHalfCellRep T j c) k (Z₁ ω) (Z₂ ω)) P)
    (hmom : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ∫⁻ ω, piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) (piHalfCellRep T j c) k (Z₁ ω) (Z₂ ω) ^ q ∂P ≤
        ENNReal.ofReal (KR k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ ((𝒯.deg k + κ) / 4)) ^ q) :
    AEMeasurable (fun ω => piHalfCellDiffRand 𝒯 Dπ DΓ nEnv T C ε θ c₀ (Z₁ ω) (Z₂ ω) j i c) P ∧
      ∫⁻ ω, piHalfCellDiffRand 𝒯 Dπ DΓ nEnv T C ε θ c₀ (Z₁ ω) (Z₂ ω) j i c ^ q ∂P ≤
        ENNReal.ofReal (c₀ * ((Fintype.card ι : ℝ) * ∑ k, KR k) * max 1 C * (C * ε ^ θ) *
          piHalfScale j ^ ((𝒯.deg i + κ) / 4)) ^ q := by
  have hs := piHalfScale_pos j
  have hm0 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  set F := Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i) with hF
  set g : ι → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
    piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) (piHalfCellRep T j c) k (Z₁ ω) (Z₂ ω) with hg
  have hgm : ∀ k, AEMeasurable (g k) P := fun k => (hmeas k).const_mul _
  have hsum : AEMeasurable (fun ω => ∑ k ∈ F, g k ω) P :=
    by
    convert Finset.aemeasurable_sum F (fun k _ => hgm k) using 1
    ext ω; simp [Finset.sum_apply]
  refine ⟨(hsum.const_mul _), ?_⟩
  set Kf : ℝ := ∑ k, KR k with hKf
  have hKfk : ∀ k, KR k ≤ Kf := fun k =>
    Finset.single_le_sum (f := KR) (fun k _ => hKR k) (Finset.mem_univ k)
  have hKf0 : 0 ≤ Kf := Finset.sum_nonneg fun k _ => hKR k
  set B : ℝ := Kf * max 1 C * (C * ε ^ θ) * piHalfScale j ^ ((𝒯.deg i + κ) / 4) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (mul_nonneg (mul_nonneg hKf0 hm0) hC) (Real.rpow_nonneg hs.le _)
  have hterm : ∀ k ∈ F, ∫⁻ ω, g k ω ^ q ∂P ≤ ENNReal.ofReal B ^ q := by
    intro k hk
    have h1 := lintegral_ofReal_mul_pow_le (P := P) (Real.rpow_nonneg hs.le
      ((𝒯.deg i - 𝒯.deg k) / 4)) q (hmom k hk)
    refine h1.trans ?_
    have hexp : piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
        (KR k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ ((𝒯.deg k + κ) / 4)) =
        KR k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ ((𝒯.deg i + κ) / 4) := by
      have : piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) * piHalfScale j ^ ((𝒯.deg k + κ) / 4) =
          piHalfScale j ^ ((𝒯.deg i + κ) / 4) := by
        rw [← Real.rpow_add hs]; congr 1; ring
      calc _ = KR k * max 1 C * (C * ε ^ θ) * (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
            piHalfScale j ^ ((𝒯.deg k + κ) / 4)) := by ring
        _ = _ := by rw [this]
    rw [hexp]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hKfk k) hm0) hC) (Real.rpow_nonneg hs.le _)
  have hMink := lintegral_sum_pow_le_card_mul (P := P) F g q hq (B := B) (fun k _ => hgm k) hterm
  have hcard : (F.card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ F
  calc ∫⁻ ω, piHalfCellDiffRand 𝒯 Dπ DΓ nEnv T C ε θ c₀ (Z₁ ω) (Z₂ ω) j i c ^ q ∂P
      = ∫⁻ ω, ENNReal.ofReal c₀ ^ q * (∑ k ∈ F, g k ω) ^ q ∂P := by
        refine lintegral_congr fun ω => ?_
        simp only [piHalfCellDiffRand, hg, hF]
        rw [mul_pow]
    _ = ENNReal.ofReal c₀ ^ q * ∫⁻ ω, (∑ k ∈ F, g k ω) ^ q ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal c₀ ^ q * ENNReal.ofReal (F.card * B) ^ q := by gcongr
    _ ≤ ENNReal.ofReal c₀ ^ q * ENNReal.ofReal ((Fintype.card ι : ℝ) * B) ^ q := by
        gcongr
    _ = ENNReal.ofReal (c₀ * ((Fintype.card ι : ℝ) * Kf) * max 1 C * (C * ε ^ θ) *
          piHalfScale j ^ ((𝒯.deg i + κ) / 4)) ^ q := by
        rw [← mul_pow, ← ENNReal.ofReal_mul hc₀]
        congr 2
        rw [hB]; ring

end RegularityStructures

end
