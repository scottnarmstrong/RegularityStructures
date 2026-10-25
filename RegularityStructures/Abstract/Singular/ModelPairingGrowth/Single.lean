/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Bound
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Weighted pairing of a model vector `Π_z e_i` with a scaled test function

Weighted versions of `Model.integrable_regPi_single_mul_of_scaled` and
`Model.tendsto_abs_pairing_regPi_single_of_scaled` for a `Model.GrowthModel`: for `g` scaled at `z`
(`IsScaledTest g z R A`), the pairing `⟨Π_z e_i, g⟩` exists and

  `|⟨Π_z e_i, g⟩| ≤ c max(1, C_Γ) C_Π (ρΠ(z) ρΓ(z)) (A R⁵) R^{deg i}`,

`c = r4ModelConstGrowth 𝒯 p qG γ`. The weight is evaluated at the base point `z`.

Source: [Hai14] = arXiv:1303.5113v4, (2.15); [Hos25] = arXiv:2310.07396v2, Remark 3.4.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}

/-- `Π_z e_i` is of local order `deg i` at `z` with growth `p + qG` and exponents in
`degreesBelowLe γ (deg i)` (weighted version of `isLocalOrder_regPi_single_degreesAtMost`). -/
theorem GrowthModel.isLocalOrderGrowth_regPi_single_top
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {i : ι} (hi : 𝒯.deg i < γ) (z : ParabolicSpace) :
    parabolicSemigroup.IsLocalOrderGrowth (fun t y => M.regPi z (Pi.single i 1) t y) z (𝒯.deg i)
      (𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i))
      (max CGam 1 * CPi * Fintype.card ι * (ρP z * ρG z)) (p + qG) :=
  M.isLocalOrderGrowth_regPi_single_in (V := ⊤) ⟨fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩
    (fun _ _ _ _ => trivial) G.moderateP G.moderateG.one_le G.nonnegG G.piBound G.gammaBound
    G.piBound_nonneg (trivial : (Pi.single i 1 : ι → ℝ) ∈ (⊤ : Submodule ℝ (ι → ℝ))) hi z

/-- For `0 < s ≤ 1`, `y ↦ (Q_s Π_z e_i)(y) g(y)` is integrable (weighted setting). -/
theorem integrable_regPi_single_mul_of_scaled_growth
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {i : ι} (hi : 𝒯.deg i < γ)
    (hg : IsScaledTest g z R A) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Integrable (fun y => M.regPi z (Pi.single i 1) s y * g y) := by
  have hloc := G.isLocalOrderGrowth_regPi_single_top hi z s ⟨hs, hs1⟩
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι * (ρP z * ρG z) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _))
      (mul_nonneg (G.moderateP.pos z).le (G.moderateG.pos z).le)
  have hpq : 0 ≤ p + qG := add_nonneg G.moderateP.nonneg_exp G.nonnegG
  set B : ℝ := max CGam 1 * CPi * Fintype.card ι * (ρP z * ρG z) * 2 ^ (p + qG) *
    ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i), s ^ (a / (4 : ℝ)) with hB
  have hmeas : AEStronglyMeasurable (fun y => M.regPi z (Pi.single i 1) s y * g y) volume :=
    ((M.measurable_regPi z _ hs).mul hg.measurable).aestronglyMeasurable
  refine (hg.integrable.norm.const_mul B).mono' hmeas (ae_of_all _ fun y => ?_)
  by_cases hy : R < parabolicNorm (y - z)
  · rw [hg.supp y hy]; simp
  · push Not at hy
    have h1 := hloc y
    have hsd : parabolicSemigroup.scaleDist y z = parabolicNorm (y - z) := rfl
    have hord : parabolicSemigroup.order = 4 := rfl
    rw [hsd, hord] at h1
    have hd1 : parabolicNorm (y - z) ≤ 1 := hy.trans hg.radius_le_one
    have hgr : (1 + parabolicNorm (y - z)) ^ (p + qG) ≤ 2 ^ (p + qG) :=
      Real.rpow_le_rpow (by linarith [parabolicNorm_nonneg (y - z)]) (by linarith) hpq
    have h2 : |M.regPi z (Pi.single i 1) s y| ≤ B := by
      refine h1.trans ?_
      rw [hB]
      have hsum : ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
          s ^ (a / (4 : ℝ)) * parabolicNorm (y - z) ^ (𝒯.deg i - a) ≤
          ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i), s ^ (a / (4 : ℝ)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hle : a ≤ 𝒯.deg i := (Finset.mem_filter.1 ha).2
        have hd : parabolicNorm (y - z) ^ (𝒯.deg i - a) ≤ 1 :=
          Real.rpow_le_one (parabolicNorm_nonneg _) hd1 (by linarith)
        calc _ ≤ s ^ (a / (4 : ℝ)) * 1 := by gcongr
          _ = _ := mul_one _
      have hS0 : 0 ≤ ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
          s ^ (a / (4 : ℝ)) * parabolicNorm (y - z) ^ (𝒯.deg i - a) :=
        Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
      generalize max CGam 1 * CPi * Fintype.card ι * (ρP z * ρG z) = c at hC ⊢
      generalize ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
        s ^ (a / (4 : ℝ)) * parabolicNorm (y - z) ^ (𝒯.deg i - a) = S at hsum hS0 ⊢
      generalize ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i), s ^ (a / (4 : ℝ)) = T at hsum ⊢
      calc c * (1 + parabolicNorm (y - z)) ^ (p + qG) * S
          ≤ c * 2 ^ (p + qG) * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgr hC) hS0
        _ ≤ c * 2 ^ (p + qG) * T :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (Real.rpow_nonneg zero_le_two _))
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- Weighted single-vector version: `⟨Π_z e_i, g⟩` exists as the limit of `∫ (Q_s Π_z e_i) g` and
`|⟨Π_z e_i, g⟩| ≤ c max(1, C_Γ) C_Π (ρΠ(z) ρΓ(z)) (A R⁵) R^{deg i}`. -/
theorem tendsto_abs_pairing_regPi_single_of_scaled_growth
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {i : ι} (hi : 𝒯.deg i < γ) (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z (Pi.single i 1) s y * g y) (𝓝[>] 0)
        (𝓝 (parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) ∧
      |parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g| ≤
        r4ModelConstGrowth 𝒯 p qG γ * (max 1 CGam * CPi) * (ρP z * ρG z) * (A * R ^ 5) *
          R ^ 𝒯.deg i := by
  obtain ⟨φ, hφ, hgeq⟩ := hg.exists_eq_smul
  obtain ⟨hT, hb⟩ := M.abs_pairing_regPi_rescaledTestFunction_le_growth G hdeg hi hφ
    hg.radius_pos hg.radius_le_one z
  have hc : 0 < A * R ^ 5 := mul_pos hg.const_pos (pow_pos hg.radius_pos 5)
  have hT' : Tendsto (fun s => ∫ y, M.regPi z (Pi.single i 1) s y * g y) (𝓝[>] 0)
      (𝓝 ((A * R ^ 5) * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1))
        (rescaledTestFunction φ R z))) := by
    refine (hT.const_mul (A * R ^ 5)).congr fun s => ?_
    rw [← integral_const_mul]
    congr 1; funext y
    rw [hgeq]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hp := parabolicSemigroup.pairing_eq_of_tendsto hT'
  refine ⟨by rw [hp]; exact hT', ?_⟩
  rw [hp, abs_mul, abs_of_pos hc]
  calc _ ≤ (A * R ^ 5) * (r4ModelConstGrowth 𝒯 p qG γ * (max 1 CGam * CPi) * (ρP z * ρG z) *
      R ^ 𝒯.deg i) := by gcongr
    _ = _ := by ring

end Model

end RegularityStructures

end
