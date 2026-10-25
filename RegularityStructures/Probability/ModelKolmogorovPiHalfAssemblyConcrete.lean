/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyCellData
public import RegularityStructures.Probability.ModelKolmogorovPiHalfBase
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADet
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySkeleton

/-!
# The concrete cell data of the `Π` half: pathwise block bound

`piHalfCellRand` and `piHalfCellDet` are the random and deterministic parts of the bound
`‖Π_x e_i(u,x)‖ ≤ (1 + G) (D + R)` obtained from the base-point block bound
(`exists_piHalfBase_block_bound`), the split `W ≤ D + R` (`piHalfCellWeightA_le_add`) and the
deterministic bound `D_k ≤ Kdet_k max(1,C) C s^{deg k / 4}`.  This is the hypothesis `hpath` of the
abstract skeleton.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The random part `c₀ ∑_{k ≤ i} s_j^{(deg i - deg k)/4} R_k(x₀)` for the cell with index `c`. -/
@[expose] noncomputable def piHalfCellRand (𝒯 : RegularityStructure ι) (Dπ : Set ι) (DΓ : Set (ι × ι))
    (nEnv : ℕ) (T : Set ParabolicSpace) (C c₀ : ℝ) (M : Model 𝒯 parabolicSemigroup) (j : ℕ)
    (i : ι) (c : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal c₀ * ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
    ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
      piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) (piHalfCellRep T j c) k M

/-- The deterministic part `c₀ (∑_{k ≤ i} Kdet_k) max(1,C) C s_j^{deg i/ℓ}`. -/
@[expose] noncomputable def piHalfCellDet (𝒯 : RegularityStructure ι) (Kdet : ι → ℝ) (c₀ C : ℝ) (j : ℕ)
    (i : ι) : ℝ :=
  c₀ * (∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), Kdet k) * max 1 C * C *
    piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)

/-- Pathwise block bound with the concrete cell data. -/
theorem exists_piHalfCell_pathwise (𝒯 : RegularityStructure ι) (γ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (Kdet : ι → ℝ) (hKdet : ∀ k, 0 ≤ Kdet k)
    (hdetA : ∀ k, ∀ C : ℝ, 0 ≤ C → ∀ {s : ℝ}, 0 < s → ∀ x₀ : ParabolicSpace,
      piHalfCellDetPartA 𝒯 Dπ DΓ nEnv C s x₀ k ≤
        ENNReal.ofReal (Kdet k * max 1 C * C * s ^ (𝒯.deg k / 4))) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (T : Set ParabolicSpace),
      T ⊆ piHalfUnitBox → ∀ (G C : ℝ), 0 ≤ G → 0 ≤ C → M.GammaBoundOn γ G T →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      ∀ i, 𝒯.deg i < γ → ∀ j : ℕ, ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j),
        ∀ (x : ParabolicSpace) (hx : x ∈ T),
          ‖M.regPi x (Pi.single i 1) u x‖ₑ ≤ ENNReal.ofReal (1 + G) *
            (ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) +
              piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ M j i (piHalfCellOf T j ⟨x, hx⟩)) := by
  obtain ⟨c₀, hc₀, hb⟩ := exists_piHalfBase_block_bound (𝒯 := 𝒯) nEnv
  refine ⟨c₀, hc₀, fun M T hT G C hG hC hΓ hm i hi j u hu x hx => ?_⟩
  have hs := piHalfScale_pos j
  have hu' : u ∈ Icc (2 * piHalfScale j) (4 * piHalfScale j) := by
    rw [two_mul_piHalfScale, four_mul_piHalfScale]; exact hu
  set x₀ := piHalfCellRep T j (piHalfCellOf T j ⟨x, hx⟩) with hx₀
  have hx₀T : x₀ ∈ T := piHalfCellRep_cellOf_mem T j ⟨x, hx⟩
  have hd := parabolicNorm_sub_piHalfCellRep_le hT j ⟨x, hx⟩
  have h1 := hb M γ i hi hs hu' T G hG hΓ x x₀ hx hx₀T hd (fun k => hm x₀ hx₀T k j)
  refine h1.trans ?_
  have hm0 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hterm : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfBaseWeight M nEnv (piHalfScale j) x₀ k ≤
        ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
          ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M := by
    intro k hk
    have hW : piHalfBaseWeight M nEnv (piHalfScale j) x₀ k ≤
        ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg k / 4)) +
          piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M :=
      (piHalfCellWeightA_le_add 𝒯 Dπ DΓ nEnv hs C x₀ k M).trans
        (add_le_add (hdetA k C hC hs x₀) le_rfl)
    refine (mul_le_mul' le_rfl hW).trans (le_of_eq ?_)
    rw [mul_add]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    have : piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) * piHalfScale j ^ (𝒯.deg k / 4) =
        piHalfScale j ^ (𝒯.deg i / 4) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    calc _ = Kdet k * max 1 C * C * (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
          piHalfScale j ^ (𝒯.deg k / 4)) := by ring
      _ = _ := by rw [this]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  have hord : parabolicSemigroup.order = 4 := rfl
  have hDet : ENNReal.ofReal c₀ * ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) =
        ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) := by
    have hnn : ∀ k, 0 ≤ Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4) := fun k =>
      mul_nonneg (mul_nonneg (mul_nonneg (hKdet k) hm0) hC) (Real.rpow_nonneg hs.le _)
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k, ← ENNReal.ofReal_mul hc₀]
    congr 1
    unfold piHalfCellDet
    rw [hord, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  calc _ ≤ ENNReal.ofReal c₀ * ENNReal.ofReal (1 + G) * (∑ k ∈ Finset.univ.filter
          (fun k => 𝒯.deg k ≤ 𝒯.deg i),
          ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
        ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
          ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (1 + G) * (ENNReal.ofReal c₀ * ∑ k ∈ Finset.univ.filter
          (fun k => 𝒯.deg k ≤ 𝒯.deg i),
          ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
        ENNReal.ofReal c₀ * ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
          ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M) := by ring
    _ = _ := by rw [hDet]; rfl

end RegularityStructures

end
