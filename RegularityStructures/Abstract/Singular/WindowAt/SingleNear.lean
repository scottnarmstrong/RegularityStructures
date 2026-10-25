/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.LocalOrderNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Window.Single
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.GeneratorProps

/-!
# Model bound for rescaled test functions in the window, near-pair `Γ`-bounds

Existence of the pairing `⟨Π_x e_i, φ^λ_x⟩` as the limit of `∫ (Q_s Π_x e_i) φ^λ_x` and the model
bound (2.15) `|⟨Π_x e_i, φ^λ_x⟩| ≤ C K₀ λ^{deg i}`, for base points `x` whose unit ball lies in the
window, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {x : ParabolicSpace} {R A : ℝ}

/-- Window form of `abs_pairing_regPi_rescaledTestFunction_le` (existence of the pairing and the
model bound (2.15)), for base points whose unit ball lies in the window. -/
theorem abs_pairing_regPi_rescaledTestFunction_le_onWindowAt_near
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hgrowth : M.HasQualitativeGrowthAt γ x)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ)
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1)
    (hball : ∀ y, parabolicNorm (y - x) ≤ 1 → y ∈ hairerTimeWindow) :
    Tendsto (fun s => ∫ y, M.regPi x (Pi.single i 1) s y * rescaledTestFunction φ lam x y)
        (𝓝[>] 0)
        (𝓝 (parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
          (rescaledTestFunction φ lam x))) ∧
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (rescaledTestFunction φ lam x)| ≤
        r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * lam ^ 𝒯.deg i := by
  obtain ⟨C', β, q, hC', hq, hcr⟩ := hgrowth.exists_crude
  have hA : ∀ a ∈ 𝒯.degreesAtMost (𝒯.deg i), -parabolicSemigroup.order < a ∧ a ≤ 𝒯.deg i := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesAtMost).1 ha
    exact ⟨hdeg j (hj.trans_lt hi), hj⟩
  have hC : 0 ≤ Fintype.card ι * (max 1 CGam * CPi) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi)
  have hloc := M.abs_regPi_single_le_of_ball_near hPi hCPi hGam hi
    (mem_hairerTimeWindow_of_ball hball) (R := 1) one_le_gammaNearRadius hball
  have hcrude : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |M.regPi x (Pi.single i 1) u y| ≤
      C' * u ^ (β / parabolicSemigroup.order) *
        (1 + parabolicSemigroup.scaleDist y x) ^ q := fun u hu y => hcr i hi u hu y
  have hmem := M.regPi_mem x (Pi.single i 1)
  have hmeas : ∀ u, 0 < u → Measurable (M.regPi x (Pi.single i 1) u) :=
    fun _ hu => M.measurable_regPi x _ hu
  have hφm := measurable_rescaledTestFunction hφ lam x
  have hψm := measurable_parabolicGenerator_rescaledTestFunction hφ lam x
  have hφi := integrable_rescaledTestFunction hφ hlam x
  have hψi := integrable_parabolicGenerator_rescaledTestFunction hφ hlam x
  have hφs : ∀ y, lam < parabolicSemigroup.scaleDist y x → rescaledTestFunction φ lam x y = 0 :=
    fun _ hy => rescaledTestFunction_eq_zero hφ.2.1 hlam hy
  have hψs : ∀ y, lam < parabolicSemigroup.scaleDist y x →
      parabolicGenerator (rescaledTestFunction φ lam x) y = 0 :=
    fun _ hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hlam hy
  have hφ1 := integral_abs_rescaledTestFunction_le hφ hlam x
  have hψ1 := integral_abs_parabolicGenerator_rescaledTestFunction_le hφ hlam x
  have hgen := isGeneratorPair_rescaledTestFunction hφ hlam x
  refine ⟨parabolicSemigroup.tendsto_integral_pairing_of_local parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hmem hmeas hA hC hC' hq
    hloc hcrude hlam hlam1 hlam1 hφm hψm hφi hψi hφs hψs hφ1 hψ1 hgen, ?_⟩
  have h := parabolicSemigroup.abs_pairing_le_of_local parabolicSemigroup_isSymmetric
    parabolicSemigroup_isMetricScale parabolicSemigroup_isJointMeasurable hmem hmeas hA hC hC' hq
    hloc hcrude hlam hlam1 hlam1 hφm hψm hφi hψi hφs hψs hφ1 hψ1 hgen
  refine h.trans ?_
  have hsub := parabolicSemigroup.pairingConst_le_of_subset
    (𝒯.degreesAtMost_subset_degreesBelow hi) fun a ha => by
      obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
      exact hdeg j hj
  have hB : 0 ≤ 16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) := by
    have := generatorTimeCoeff_pos
    have := generatorSpaceCoeff_pos
    positivity
  have hl : 0 ≤ lam ^ 𝒯.deg i := Real.rpow_nonneg hlam.le _
  calc Fintype.card ι * (max 1 CGam * CPi) *
        parabolicSemigroup.pairingConst (𝒯.degreesAtMost (𝒯.deg i)) *
        (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff)) * lam ^ 𝒯.deg i
      ≤ Fintype.card ι * (max 1 CGam * CPi) *
        parabolicSemigroup.pairingConst (𝒯.degreesBelow γ) *
        (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff)) * lam ^ 𝒯.deg i := by
        gcongr
    _ = r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * lam ^ 𝒯.deg i := by
        rw [r4ModelConst]
        ring

end Model

end RegularityStructures

end
