/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfFactorBound
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADet

/-!
# The cell weight for the difference of two models (A3): definitions, pathwise bound, term moments

`piHalfCellDiffWeightA` is `∫⁻ w, E^n_s(x₀ - w) ‖(Q_s (Π¹_{x₀} - Π²_{x₀}) e_k)(w)‖`.  Pathwise,
`Π¹_{x₀} e_k - Π²_{x₀} e_k = ∑_j (Γ¹_j (Π¹_j - Π²_j) + (Γ¹_j - Γ²_j) Π²_j)` and the summands
`piHalfCellDiffTermA` (indexed by `(j, true)` and `(j, false)`) over the indices with a random
factor dominate the remainder after subtracting the deterministic majorant
`piHalfCellDiffDetFunA`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The summands `‖Γ¹_j‖ ‖Π¹_j - Π²_j‖` (for `true`) and `‖Γ¹_j - Γ²_j‖ ‖Π²_j‖` (for `false`). -/
def piHalfCellDiffTermA (𝒯 : RegularityStructure ι) (s : ℝ) (x₀ : ParabolicSpace) (k : ι)
    (Z₁ Z₂ : Model 𝒯 parabolicSemigroup) (jb : ι × Bool) (w : ParabolicSpace) : ℝ≥0∞ :=
  if jb.2 then ‖Z₁.gammaMap w x₀ (Pi.single k 1) jb.1‖ₑ *
      ‖Z₁.regPi w (Pi.single jb.1 1) s w - Z₂.regPi w (Pi.single jb.1 1) s w‖ₑ
  else ‖Z₁.gammaMap w x₀ (Pi.single k 1) jb.1 - Z₂.gammaMap w x₀ (Pi.single k 1) jb.1‖ₑ *
      ‖Z₂.regPi w (Pi.single jb.1 1) s w‖ₑ

/-- The deterministic majorant for the difference: coefficient `2 max(1,C) C ε^θ`. -/
def piHalfCellDiffDetFunA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι)
    (C ε θ s : ℝ) (x₀ w : ParabolicSpace) : ℝ :=
  piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k (2 * max 1 C * (C * ε ^ θ)) s x₀ w

/-- The random remainder for the difference. -/
def piHalfCellDiffRandRemA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι)
    (C ε θ s : ℝ) (x₀ : ParabolicSpace) (Z₁ Z₂ : Model 𝒯 parabolicSemigroup)
    (w : ParabolicSpace) : ℝ≥0∞ :=
  ‖Z₁.regPi x₀ (Pi.single k 1) s w - Z₂.regPi x₀ (Pi.single k 1) s w‖ₑ -
    ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ w)

/-- The cell weight of the difference. -/
def piHalfCellDiffWeightA (𝒯 : RegularityStructure ι) (n : ℕ) (s : ℝ) (x₀ : ParabolicSpace)
    (k : ι) (Z₁ Z₂ : Model 𝒯 parabolicSemigroup) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    ‖Z₁.regPi x₀ (Pi.single k 1) s w - Z₂.regPi x₀ (Pi.single k 1) s w‖ₑ

/-- The deterministic part of the difference weight. -/
def piHalfCellDiffDetPartA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (n : ℕ)
    (C ε θ s : ℝ) (x₀ : ParabolicSpace) (k : ι) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ w)

/-- The random part of the difference weight. -/
def piHalfCellDiffRandPartA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (n : ℕ)
    (C ε θ s : ℝ) (x₀ : ParabolicSpace) (k : ι) (Z₁ Z₂ : Model 𝒯 parabolicSemigroup) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    piHalfCellDiffRandRemA 𝒯 Dπ DΓ k C ε θ s x₀ Z₁ Z₂ w

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The difference weight is at most `D + R`. -/
theorem piHalfCellDiffWeightA_le_add (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (n : ℕ) {s : ℝ} (hs : 0 < s) (C ε θ : ℝ) (x₀ : ParabolicSpace) (k : ι)
    (Z₁ Z₂ : Model 𝒯 parabolicSemigroup) :
    piHalfCellDiffWeightA 𝒯 n s x₀ k Z₁ Z₂ ≤
      piHalfCellDiffDetPartA 𝒯 Dπ DΓ n C ε θ s x₀ k +
        piHalfCellDiffRandPartA 𝒯 Dπ DΓ n C ε θ s x₀ k Z₁ Z₂ := by
  unfold piHalfCellDiffWeightA piHalfCellDiffDetPartA piHalfCellDiffRandPartA
  have hE : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w))) :=
    (measurable_kernelBlockEnvelope_shift n hs x₀).ennreal_ofReal
  have hD : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
      ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ w)) :=
    hE.mul (measurable_piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k _ s x₀).ennreal_ofReal
  rw [← lintegral_add_left hD]
  refine lintegral_mono fun w => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left le_add_tsub zero_le

/-- The integral of the deterministic majorant of the difference. -/
theorem exists_piHalfCellDiffDetPartA_le (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (k : ι) {n : ℕ}
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → 𝒯.deg k - 𝒯.deg j + 1 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C ε θ : ℝ), 0 ≤ C → 0 ≤ ε → ∀ {s : ℝ}, 0 < s → ∀ (x₀ : ParabolicSpace),
      piHalfCellDiffDetPartA 𝒯 Dπ DΓ n C ε θ s x₀ k ≤
        ENNReal.ofReal (K * max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg k / 4)) := by
  obtain ⟨K, hK, h⟩ := exists_piHalfCellDetCoeffPartA_le 𝒯 Dπ DΓ k hn
  refine ⟨2 * K, by positivity, fun C ε θ hC hε s hs x₀ => ?_⟩
  have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have := h (2 * max 1 C * (C * ε ^ θ))
    (mul_nonneg (mul_nonneg (by norm_num) hCm) (mul_nonneg hC (Real.rpow_nonneg hε _))) hs x₀
  refine this.trans (le_of_eq ?_)
  congr 1
  ring

end RegularityStructures

end
