/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Probability.ModelKolmogorovPiHalfWeightedMoment

/-!
# The cell weight `W` of the parallel Pi half: definitions

For a model `Z`, a scale `s`, a base point `x₀` and a basis index `k`,
`piHalfCellWeightA 𝒯 n s x₀ k Z = ∫⁻ w, E^n_s(x₀ - w) ‖(Q_s Π_{x₀} e_k)(w)‖`
(off-diagonal at the fixed base point `x₀`).  Pathwise, `‖(Q_s Π_{x₀} e_k)(w)‖` is at most the
deterministic function `piHalfCellDetFunA` plus the remainder `piHalfCellRandRemA`, which is
dominated by the summands `‖(Γ_{w x₀} e_k)_j‖ ‖(Q_s Π_w e_j)(w)‖` over the indices
`piHalfRandIndexA` having a random factor.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The summand `‖(Γ_{w x₀} e_k)_j‖ ‖(Q_s Π_w e_j)(w)‖`. -/
def piHalfCellTermA (𝒯 : RegularityStructure ι) (s : ℝ) (x₀ : ParabolicSpace) (k : ι)
    (Z : Model 𝒯 parabolicSemigroup) (j : ι) (w : ParabolicSpace) : ℝ≥0∞ :=
  ‖Z.gammaMap w x₀ (Pi.single k 1) j‖ₑ * ‖Z.regPi w (Pi.single j 1) s w‖ₑ

open scoped Classical in
/-- The indices `j` with `deg j ≤ deg k`. -/
def piHalfLowIndexA (𝒯 : RegularityStructure ι) (k : ι) : Finset ι :=
  Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k

open scoped Classical in
/-- The indices whose two factors are both deterministic: `j ∈ Dπ`, and the `Γ` coefficient is
trivial (`deg j = deg k`: it is `1` for `j = k`, `0` otherwise) or `(k, j) ∈ DΓ`. -/
def piHalfDetIndexA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι) :
    Finset ι :=
  Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k ∧
    (j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ))

open scoped Classical in
/-- The indices with at least one random factor. -/
def piHalfRandIndexA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι) :
    Finset ι :=
  Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k ∧
    ¬ (j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ))

/-- The deterministic majorant with a free coefficient `A`:
`∑_{j det} A s^{deg j/4} d(x₀, w)^{deg k - deg j}`. -/
def piHalfCellDetFunCoeffA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι)
    (A s : ℝ) (x₀ w : ParabolicSpace) : ℝ :=
  ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k,
    A * s ^ (𝒯.deg j / 4) * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)

/-- The deterministic majorant `Det_k(w) = ∑_{j det} max(1,C) C s^{deg j/4} d(x₀, w)^{deg k - deg j}`. -/
def piHalfCellDetFunA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι)
    (C s : ℝ) (x₀ w : ParabolicSpace) : ℝ :=
  piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k (max 1 C * C) s x₀ w

/-- The random remainder `R'_k = (‖Q_s Π_{x₀} e_k (w)‖ - Det_k(w))⁺`. -/
def piHalfCellRandRemA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι)
    (C s : ℝ) (x₀ : ParabolicSpace) (Z : Model 𝒯 parabolicSemigroup) (w : ParabolicSpace) :
    ℝ≥0∞ :=
  ‖Z.regPi x₀ (Pi.single k 1) s w‖ₑ -
    ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ w)

/-- The cell weight `W = ∫⁻ w, E^n_s(x₀ - w) ‖(Q_s Π_{x₀} e_k)(w)‖`. -/
def piHalfCellWeightA (𝒯 : RegularityStructure ι) (n : ℕ) (s : ℝ) (x₀ : ParabolicSpace) (k : ι)
    (Z : Model 𝒯 parabolicSemigroup) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) * ‖Z.regPi x₀ (Pi.single k 1) s w‖ₑ

/-- The deterministic part `D = ∫⁻ w, E^n_s(x₀ - w) Det_k(w)`. -/
def piHalfCellDetPartA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (n : ℕ)
    (C s : ℝ) (x₀ : ParabolicSpace) (k : ι) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ w)

/-- The random part `R = ∫⁻ w, E^n_s(x₀ - w) R'_k(w)`. -/
def piHalfCellRandPartA (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι)) (n : ℕ)
    (C s : ℝ) (x₀ : ParabolicSpace) (k : ι) (Z : Model 𝒯 parabolicSemigroup) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    piHalfCellRandRemA 𝒯 Dπ DΓ k C s x₀ Z w

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalfDetIndexA_union (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι))
    (k : ι) (f : ι → ℝ≥0∞) :
    ∑ j ∈ piHalfLowIndexA 𝒯 k, f j =
      ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, f j + ∑ j ∈ piHalfRandIndexA 𝒯 Dπ DΓ k, f j := by
  classical
  unfold piHalfLowIndexA piHalfDetIndexA piHalfRandIndexA
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k)
    (fun j => j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ))]
  simp only [Finset.filter_filter]

theorem measurable_piHalfCellDetFunCoeffA (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (k : ι) (A s : ℝ) (x₀ : ParabolicSpace) :
    Measurable (piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k A s x₀) := by
  unfold piHalfCellDetFunCoeffA
  refine Finset.measurable_sum _ fun j _ => Measurable.const_mul ?_ _
  exact ((continuous_parabolicNorm.comp (continuous_const.sub continuous_id)).measurable).pow_const _

theorem measurable_piHalfCellDetFunA (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (k : ι) (C s : ℝ) (x₀ : ParabolicSpace) :
    Measurable (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀) :=
  measurable_piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k _ s x₀

/-- The cell weight is at most `D + R`. -/
theorem piHalfCellWeightA_le_add (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι))
    (n : ℕ) {s : ℝ} (hs : 0 < s) (C : ℝ) (x₀ : ParabolicSpace) (k : ι)
    (Z : Model 𝒯 parabolicSemigroup) :
    piHalfCellWeightA 𝒯 n s x₀ k Z ≤
      piHalfCellDetPartA 𝒯 Dπ DΓ n C s x₀ k + piHalfCellRandPartA 𝒯 Dπ DΓ n C s x₀ k Z := by
  unfold piHalfCellWeightA piHalfCellDetPartA piHalfCellRandPartA
  have hE : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w))) :=
    (measurable_kernelBlockEnvelope_shift n hs x₀).ennreal_ofReal
  have hD : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
      ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ w)) :=
    hE.mul (measurable_piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀).ennreal_ofReal
  rw [← lintegral_add_left hD]
  refine lintegral_mono fun w => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left le_add_tsub zero_le

end RegularityStructures

end
