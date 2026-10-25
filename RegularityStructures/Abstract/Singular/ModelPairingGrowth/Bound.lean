/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Bundle
public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Analysis.Semigroup.PairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Weighted model bound (2.15) against rescaled test functions on `ℝ⁴`

Weighted version of `Model.abs_pairing_regPi_rescaledTestFunction_le`: for a model with the
weighted bounds `PiBoundGrowth`, `GammaBoundGrowth` (`Model.GrowthModel`), `deg i < γ`, all
homogeneities below `γ` larger than `-4`, `φ ∈ B^4` and `0 < λ ≤ 1`, the pairing
`⟨Π_x e_i, φ^λ_x⟩` exists and

  `|⟨Π_x e_i, φ^λ_x⟩| ≤ c · max(1, C_Γ) C_Π · (ρΠ(x) ρΓ(x)) · λ^{deg i}`,

with `c = r4ModelConstGrowth 𝒯 p qG γ` depending only on `𝒯, p, qG, γ`; the weight is evaluated
at the base point `x`. The proof is the local order with growth
`Model.isLocalOrderGrowth_regPi_single_in` (for the full sector `⊤`) combined with
`abs_pairing_le_of_growth`.

Source: [Hai14] = arXiv:1303.5113v4, (2.15); [Hos25] = arXiv:2310.07396v2, Remark 3.4.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant of the weighted test-function model bound on `ℝ⁴`. -/
def r4ModelConstGrowth (𝒯 : RegularityStructure ι) (p qG γ : ℝ) : ℝ :=
  2 ^ (p + qG) * Fintype.card ι * parabolicSemigroup.pairingConst (𝒯.degreesBelow γ) *
    (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff))

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

variable {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup)
  {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- **Weighted model bound (2.15) on `ℝ⁴`**: the pairing `⟨Π_x e_i, φ^λ_x⟩` exists and is
bounded by `c max(1, C_Γ) C_Π ρΠ(x) ρΓ(x) λ^{deg i}`. -/
theorem abs_pairing_regPi_rescaledTestFunction_le_growth
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ)
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (x : ParabolicSpace) :
    Tendsto (fun s => ∫ y, M.regPi x (Pi.single i 1) s y * rescaledTestFunction φ lam x y)
        (𝓝[>] 0)
        (𝓝 (parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
          (rescaledTestFunction φ lam x))) ∧
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (rescaledTestFunction φ lam x)| ≤
        r4ModelConstGrowth 𝒯 p qG γ * (max 1 CGam * CPi) * (ρP x * ρG x) * lam ^ 𝒯.deg i := by
  have hsec : 𝒯.IsSector (⊤ : Submodule ℝ (ι → ℝ)) :=
    ⟨fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  have hloc := M.isLocalOrderGrowth_regPi_single_in hsec (fun _ _ _ _ => trivial)
    G.moderateP G.moderateG.one_le G.nonnegG G.piBound G.gammaBound G.piBound_nonneg
    (trivial : (Pi.single i 1 : ι → ℝ) ∈ (⊤ : Submodule ℝ (ι → ℝ))) hi x
  have hA : ∀ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i), -parabolicSemigroup.order < a ∧
      a ≤ 𝒯.deg i := by
    intro a ha
    obtain ⟨hb, hle⟩ := Finset.mem_filter.1 ha
    obtain ⟨j, -, hj, rfl⟩ := (𝒯.mem_degreesBelowIn _).1 hb
    exact ⟨hdeg j hj, hle⟩
  have hρ0 : 0 ≤ ρP x * ρG x :=
    mul_nonneg (G.moderateP.pos x).le (G.moderateG.pos x).le
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _)) hρ0
  have hq : 0 ≤ p + qG := add_nonneg G.moderateP.nonneg_exp G.nonnegG
  have hmem := M.regPi_mem x (Pi.single i 1)
  have hmeas : ∀ u, 0 < u → Measurable (M.regPi x (Pi.single i 1) u) :=
    fun _ hu => M.measurable_regPi x _ hu
  have hψ := integral_abs_parabolicGenerator_rescaledTestFunction_le hφ hlam x
  have hφ1 := integral_abs_rescaledTestFunction_le hφ hlam x
  have hgen := parabolicSemigroup_isGeneratorPair (contDiff_rescaledTestFunction_of_mem hφ lam x)
    (hasCompactSupport_rescaledTestFunction hφ hlam x)
  have hord : parabolicSemigroup.order = 4 := rfl
  have hψ' : ∫ y, |parabolicGenerator (rescaledTestFunction φ lam x) y| ≤
      (16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff)) *
        lam ^ (-parabolicSemigroup.order) := by
    rw [hord]; exact hψ
  have hlocal := hloc
  refine ⟨parabolicSemigroup.tendsto_integral_pairing_of_growth parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hmem hmeas hA hC hq
    hlocal hlam hlam1 (measurable_rescaledTestFunction hφ lam x)
    (measurable_parabolicGenerator_rescaledTestFunction hφ lam x)
    (integrable_rescaledTestFunction hφ hlam x)
    (integrable_parabolicGenerator_rescaledTestFunction hφ hlam x)
    (fun _ hy => rescaledTestFunction_eq_zero hφ.2.1 hlam hy)
    (fun _ hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hlam hy)
    hφ1 hψ' hgen, ?_⟩
  have h := parabolicSemigroup.abs_pairing_le_of_growth parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hmem hmeas hA hC hq
    hlocal hlam hlam1 (measurable_rescaledTestFunction hφ lam x)
    (measurable_parabolicGenerator_rescaledTestFunction hφ lam x)
    (integrable_rescaledTestFunction hφ hlam x)
    (integrable_parabolicGenerator_rescaledTestFunction hφ hlam x)
    (fun _ hy => rescaledTestFunction_eq_zero hφ.2.1 hlam hy)
    (fun _ hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hlam hy)
    hφ1 hψ' hgen
  refine h.trans ?_
  have hsub := parabolicSemigroup.pairingConst_le_of_subset
    (A := 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i)) (A' := 𝒯.degreesBelow γ)
    ((Finset.filter_subset _ _).trans (𝒯.degreesBelowIn_subset ⊤)) fun a ha => by
      obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
      exact hdeg j hj
  have hB : 0 ≤ 16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) := by
    have := generatorTimeCoeff_pos
    have := generatorSpaceCoeff_pos
    positivity
  have h2 : 0 ≤ (2 : ℝ) ^ (p + qG) := Real.rpow_nonneg zero_le_two _
  have hl : 0 ≤ lam ^ 𝒯.deg i := Real.rpow_nonneg hlam.le _
  have hCP : 0 ≤ max 1 CGam * CPi :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) G.piBound_nonneg
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  rw [max_comm CGam 1, r4ModelConstGrowth]
  calc 2 ^ (p + qG) * (max 1 CGam * CPi * Fintype.card ι * (ρP x * ρG x)) *
        parabolicSemigroup.pairingConst (𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i)) *
        (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff)) * lam ^ 𝒯.deg i
      ≤ 2 ^ (p + qG) * (max 1 CGam * CPi * Fintype.card ι * (ρP x * ρG x)) *
        parabolicSemigroup.pairingConst (𝒯.degreesBelow γ) *
        (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff)) * lam ^ 𝒯.deg i := by
        gcongr
    _ = _ := by ring

end Model

end RegularityStructures

end
