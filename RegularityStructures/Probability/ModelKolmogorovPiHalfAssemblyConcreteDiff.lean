/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyConcrete
public import RegularityStructures.Probability.ModelKolmogorovPiHalfBaseDiff
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADiff

/-!
# The concrete cell data of the `Π` half: pathwise block bound, difference version

`‖(Π¹ - Π²)_x e_i(u,x)‖ ≤ (1 + G)(D¹² + R¹²) + Gd (D² + R²)` from `exists_piHalfBase_block_bound_diff`
and the splits `W ≤ D + R` of the difference weight and of the weight of the second model.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The random part for the difference of two models. -/
@[expose] noncomputable def piHalfCellDiffRand (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (T : Set ParabolicSpace) (C ε θ c₀ : ℝ)
    (M M' : Model 𝒯 parabolicSemigroup) (j : ℕ) (i : ι) (c : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal c₀ * ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
    ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
      piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) (piHalfCellRep T j c) k M M'

/-- The deterministic part with free coefficients `m`, `C'`. -/
@[expose] noncomputable def piHalfCellDetG (𝒯 : RegularityStructure ι) (Kdet : ι → ℝ) (c₀ m C' : ℝ)
    (j : ℕ) (i : ι) : ℝ :=
  c₀ * (∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), Kdet k) * m * C' *
    piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)

/-- Pathwise block bound for the difference. -/
theorem exists_piHalfCell_pathwise_diff (𝒯 : RegularityStructure ι) (γ θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (Kdet KdetD : ι → ℝ) (hKdet : ∀ k, 0 ≤ Kdet k)
    (hKdetD : ∀ k, 0 ≤ KdetD k)
    (hdetA : ∀ k, ∀ C : ℝ, 0 ≤ C → ∀ {s : ℝ}, 0 < s → ∀ x₀ : ParabolicSpace,
      piHalfCellDetPartA 𝒯 Dπ DΓ nEnv C s x₀ k ≤
        ENNReal.ofReal (Kdet k * max 1 C * C * s ^ (𝒯.deg k / 4)))
    (hdetD : ∀ k, ∀ C ε : ℝ, 0 ≤ C → 0 ≤ ε → ∀ {s : ℝ}, 0 < s → ∀ x₀ : ParabolicSpace,
      piHalfCellDiffDetPartA 𝒯 Dπ DΓ nEnv C ε θ s x₀ k ≤
        ENNReal.ofReal (KdetD k * max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg k / 4))) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (M M' : Model 𝒯 parabolicSemigroup) (T : Set ParabolicSpace),
      T ⊆ piHalfUnitBox → ∀ (G Gd C ε : ℝ), 0 ≤ G → 0 ≤ Gd → 0 ≤ C → 0 ≤ ε →
      M.GammaBoundOn γ G T → Model.GammaDiffBoundOn M M' γ Gd T →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M'.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      ∀ i, 𝒯.deg i < γ → ∀ j : ℕ, ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j),
        ∀ (x : ParabolicSpace) (hx : x ∈ T),
          ‖M.regPi x (Pi.single i 1) u x - M'.regPi x (Pi.single i 1) u x‖ₑ ≤
            ENNReal.ofReal (1 + G) *
              (ENNReal.ofReal (piHalfCellDetG 𝒯 KdetD c₀ (max 1 C) (C * ε ^ θ) j i) +
                piHalfCellDiffRand 𝒯 Dπ DΓ nEnv T C ε θ c₀ M M' j i (piHalfCellOf T j ⟨x, hx⟩)) +
            ENNReal.ofReal Gd *
              (ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) +
                piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ M' j i (piHalfCellOf T j ⟨x, hx⟩)) := by
  obtain ⟨c₀, hc₀, hb⟩ := exists_piHalfBase_block_bound_diff (𝒯 := 𝒯) nEnv
  refine ⟨c₀, hc₀, fun M M' T hT G Gd C ε hG hGd hC hε hΓ hΓd hm hm' i hi j u hu x hx => ?_⟩
  have hs := piHalfScale_pos j
  have hu' : u ∈ Icc (2 * piHalfScale j) (4 * piHalfScale j) := by
    rw [two_mul_piHalfScale, four_mul_piHalfScale]; exact hu
  set x₀ := piHalfCellRep T j (piHalfCellOf T j ⟨x, hx⟩) with hx₀
  have hx₀T : x₀ ∈ T := piHalfCellRep_cellOf_mem T j ⟨x, hx⟩
  have hd := parabolicNorm_sub_piHalfCellRep_le hT j ⟨x, hx⟩
  have h1 := hb M M' γ i hi hs hu' T G Gd hG hGd hΓ hΓd x x₀ hx hx₀T hd
    (fun k => hm x₀ hx₀T k j) (fun k => hm' x₀ hx₀T k j)
  refine h1.trans ?_
  have hm0 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hCd : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  have hord : parabolicSemigroup.order = 4 := rfl
  have hexp : ∀ k : ι, piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) * piHalfScale j ^ (𝒯.deg k / 4) =
      piHalfScale j ^ (𝒯.deg i / 4) := fun k => by
    rw [← Real.rpow_add hs]; congr 1; ring
  -- the two weights
  have hW1 : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
        piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k ≤
      ENNReal.ofReal (KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg i / 4)) +
        ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) x₀ k M M' := by
    intro k _
    have hW : piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k ≤
        ENNReal.ofReal (KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg k / 4)) +
          piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) x₀ k M M' :=
      (piHalfCellDiffWeightA_le_add 𝒯 Dπ DΓ nEnv hs C ε θ x₀ k M M').trans
        (add_le_add (hdetD k C ε hC hε hs x₀) le_rfl)
    refine (mul_le_mul' le_rfl hW).trans (le_of_eq ?_)
    rw [mul_add]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    calc _ = KdetD k * max 1 C * (C * ε ^ θ) * (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
          piHalfScale j ^ (𝒯.deg k / 4)) := by ring
      _ = _ := by rw [hexp k]
  have hW2 : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
        piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k ≤
      ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
        ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M' := by
    intro k _
    have hW : piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k ≤
        ENNReal.ofReal (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg k / 4)) +
          piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M' :=
      (piHalfCellWeightA_le_add 𝒯 Dπ DΓ nEnv hs C x₀ k M').trans
        (add_le_add (hdetA k C hC hs x₀) le_rfl)
    refine (mul_le_mul' le_rfl hW).trans (le_of_eq ?_)
    rw [mul_add]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    calc _ = Kdet k * max 1 C * C * (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
          piHalfScale j ^ (𝒯.deg k / 4)) := by ring
      _ = _ := by rw [hexp k]
  set F := Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i) with hF
  have hDetD : ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal
      (KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg i / 4)) =
        ENNReal.ofReal (piHalfCellDetG 𝒯 KdetD c₀ (max 1 C) (C * ε ^ θ) j i) := by
    have hnn : ∀ k, 0 ≤ KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg i / 4) :=
      fun k => mul_nonneg (mul_nonneg (mul_nonneg (hKdetD k) hm0) hCd) (Real.rpow_nonneg hs.le _)
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k, ← ENNReal.ofReal_mul hc₀]
    congr 1
    unfold piHalfCellDetG
    rw [hord, hF, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hDet2 : ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal
      (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) =
        ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) := by
    have hnn : ∀ k, 0 ≤ Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4) :=
      fun k => mul_nonneg (mul_nonneg (mul_nonneg (hKdet k) hm0) hC) (Real.rpow_nonneg hs.le _)
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k, ← ENNReal.ofReal_mul hc₀]
    congr 1
    unfold piHalfCellDet
    rw [hord, hF, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hA : ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
        (ENNReal.ofReal (1 + G) * piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k +
          ENNReal.ofReal Gd * piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k) =
      ENNReal.ofReal (1 + G) * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k +
        ENNReal.ofReal Gd * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hB1 := Finset.sum_le_sum hW1
  have hB2 := Finset.sum_le_sum hW2
  rw [Finset.sum_add_distrib] at hB1 hB2
  calc ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
        (ENNReal.ofReal (1 + G) * piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k +
          ENNReal.ofReal Gd * piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k)
      = ENNReal.ofReal c₀ * (ENNReal.ofReal (1 + G) * ∑ k ∈ F,
          ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfBaseDiffWeight M M' nEnv (piHalfScale j) x₀ k +
        ENNReal.ofReal Gd * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
          piHalfBaseWeight M' nEnv (piHalfScale j) x₀ k) := by rw [hA]
    _ ≤ ENNReal.ofReal c₀ * (ENNReal.ofReal (1 + G) * (∑ k ∈ F, ENNReal.ofReal
            (KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg i / 4)) +
          ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) x₀ k M M') +
        ENNReal.ofReal Gd * (∑ k ∈ F, ENNReal.ofReal
            (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
          ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M')) := by
        gcongr
    _ = ENNReal.ofReal (1 + G) * (ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal
            (KdetD k * max 1 C * (C * ε ^ θ) * piHalfScale j ^ (𝒯.deg i / 4)) +
          ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ (piHalfScale j) x₀ k M M') +
        ENNReal.ofReal Gd * (ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal
            (Kdet k * max 1 C * C * piHalfScale j ^ (𝒯.deg i / 4)) +
          ENNReal.ofReal c₀ * ∑ k ∈ F, ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
            piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) x₀ k M') := by ring
    _ = _ := by rw [hDetD, hDet2]; rfl

end RegularityStructures

end
