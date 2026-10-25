/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.LocalOrderNear
public import RegularityStructures.Abstract.Singular.WindowAt.SingleNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Window.Single
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Single-vector model bound for scaled test functions, near-pair `Γ`-bounds

For `0 < s ≤ 1`, `y ↦ (Q_s Π_z e_i)(y) g(y)` is integrable, and `⟨Π_z e_i, g⟩` exists as the limit
of `∫ (Q_s Π_z e_i) g` and obeys the bound `C (A R⁵) R^{deg i}`,
`C = r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π`, in the window setting, for models whose `Γ`-bounds hold
only for near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in
place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {z : ParabolicSpace} {R A : ℝ}

/-- For `0 < s ≤ 1`, `y ↦ (Q_s Π_z e_i)(y) g(y)` is integrable (window setting). -/
theorem integrable_regPi_single_mul_of_scaled_onWindowAt_near
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) {i : ι} (hi : 𝒯.deg i < γ)
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow)
    (hg : IsScaledTest g z R A) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Integrable (fun y => M.regPi z (Pi.single i 1) s y * g y) := by
  have hloc := M.abs_regPi_single_le_of_ball_near hPi hCPi hGam hi
    (mem_hairerTimeWindow_of_ball hball) (R := 1) one_le_gammaNearRadius hball s ⟨hs, hs1⟩
  have hC : 0 ≤ (Fintype.card ι : ℝ) * (max 1 CGam * CPi) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi)
  set B : ℝ := Fintype.card ι * (max 1 CGam * CPi) *
    ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i), s ^ (a / (4 : ℝ)) with hB
  have hmeas : AEStronglyMeasurable (fun y => M.regPi z (Pi.single i 1) s y * g y) volume :=
    ((M.measurable_regPi z _ hs).mul hg.measurable).aestronglyMeasurable
  refine (hg.integrable.norm.const_mul B).mono' hmeas (ae_of_all _ fun y => ?_)
  by_cases hy : R < parabolicNorm (y - z)
  · rw [hg.supp y hy]; simp
  · push Not at hy
    have hyb : parabolicSemigroup.scaleDist y z ≤ 1 := hy.trans hg.radius_le_one
    have h1 := hloc y hyb
    have hsd : parabolicSemigroup.scaleDist y z = parabolicNorm (y - z) := rfl
    have hord : parabolicSemigroup.order = 4 := rfl
    rw [hsd, hord] at h1
    have h2 : |M.regPi z (Pi.single i 1) s y| ≤ B := by
      refine h1.trans ?_
      rw [hB]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hC
      obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesAtMost).1 ha
      have hd : parabolicNorm (y - z) ^ (𝒯.deg i - 𝒯.deg j) ≤ 1 :=
        Real.rpow_le_one (parabolicNorm_nonneg _) (hy.trans hg.radius_le_one) (by linarith)
      calc _ ≤ s ^ (𝒯.deg j / (4 : ℝ)) * 1 := by
            gcongr
        _ = _ := mul_one _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- Window single-vector version: `⟨Π_z e_i, g⟩` exists as the limit of `∫ (Q_s Π_z e_i) g` and
obeys `C (A R⁵) R^{deg i}`, `C = r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π`. -/
theorem tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hgrowth : M.HasQualitativeGrowthAt γ z)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ)
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow)
    (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z (Pi.single i 1) s y * g y) (𝓝[>] 0)
        (𝓝 (parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) ∧
      |parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g| ≤
        r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) * R ^ 𝒯.deg i := by
  obtain ⟨φ, hφ, hgeq⟩ := hg.exists_eq_smul
  obtain ⟨hT, hb⟩ := M.abs_pairing_regPi_rescaledTestFunction_le_onWindowAt_near hPi hCPi hGam hgrowth
    hdeg hi hφ hg.radius_pos hg.radius_le_one hball
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
  calc _ ≤ (A * R ^ 5) * (r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * R ^ 𝒯.deg i) := by gcongr
    _ = _ := by ring

end Model

end RegularityStructures

end
