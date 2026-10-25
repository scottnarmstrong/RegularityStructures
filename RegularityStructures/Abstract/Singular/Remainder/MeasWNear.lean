/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.LipschitzWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Continuity and measurability of `R_γ f`, near-pair `Γ`-bounds

`x ↦ ⟨R f, D^k R(x − ·)⟩` is continuous on `{x₀ ≤ T}` (`continuousOn_remPairing_lineIter_win_near`),
hence so is `x ↦ R_γ f(x)` (`continuousOn_remVec_win_near`), and `x ↦ 1_{(0,T] × ℝ³}(x) R_γ f(x)` is
measurable (`measurable_indicator_timeSlab_remVec_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology MeasureTheory

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem continuousOn_remPairing_lineIter_win_near {M : Model 𝒯 parabolicSemigroup}
    {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r) (k : Fin 4 →₀ ℕ) :
    ContinuousOn (fun x : ParabolicSpace =>
      M.remPairing f (fun y => lineIter (multiDirs k) r (x - y)))
      {x : ParabolicSpace | x.1 ≤ T} := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_remPairing_sub_le_win_near 𝒯 γ η α S.hdeg S.hγ S.hαγ S.hαη hr k
  intro x₀ hx₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set L : ℝ := C * (max 1 CGam * CPi) * Cf with hL
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hL0 : 0 ≤ L := by have := S.hCf; positivity
  refine ⟨min 1 (ε / (L + 1)), lt_min one_pos (by positivity), fun x hx hxd => ?_⟩
  have hxd' : ‖x - x₀‖ < min 1 (ε / (L + 1)) := by simpa [dist_eq_norm] using hxd
  rw [Real.dist_eq]
  have h1 := hC M f T Cf CPi CGam S x x₀ hx hx₀ (hxd'.trans_le (min_le_left _ _)).le
  refine lt_of_le_of_lt h1 ?_
  have h2 : ‖x - x₀‖ < ε / (L + 1) := hxd'.trans_le (min_le_right _ _)
  calc L * ‖x - x₀‖ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left h2.le hL0
    _ = ε * (L / (L + 1)) := by ring
    _ < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one (by positivity)]; linarith
    _ = ε := mul_one ε

theorem continuousOn_remVec_win_near {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    {γ η α Cf CPi CGam T : ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') :
    ContinuousOn (M.remVecG r P γ f) {x : ParabolicSpace | x.1 ≤ T} := by
  classical
  unfold Model.remVecG
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases hp : polyDeg N' k < γ + 2
  · simp only [hp, ↓reduceIte]
    exact ((continuousOn_remPairing_lineIter_win_near S hr k.1).div_const _).smul continuousOn_const
  · simp only [hp, ↓reduceIte]
    exact continuousOn_const

/-- `x ↦ 1_{(0,T] × ℝ³}(x) R_γ f(x)` is measurable. -/
theorem measurable_indicator_timeSlab_remVec_win_near {M : Model 𝒯 parabolicSemigroup}
    {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') :
    Measurable (fun x : ParabolicSpace => (timeSlab T).indicator (M.remVecG r P γ f) x) := by
  classical
  set A : Set ParabolicSpace := {x | x.1 ≤ T} with hA
  have hAm : MeasurableSet A := measurableSet_le measurable_fst measurable_const
  have hpw : Measurable (A.piecewise (M.remVecG r P γ f) fun _ => 0) :=
    ContinuousOn.measurable_piecewise (continuousOn_remVec_win_near S hr P) continuousOn_const hAm
  have hsub : timeSlab T ⊆ A := fun x hx => hx.2
  have e : (fun x : ParabolicSpace => (timeSlab T).indicator (M.remVecG r P γ f) x) =
      fun x => (timeSlab T).indicator (A.piecewise (M.remVecG r P γ f) fun _ => 0) x := by
    funext x
    by_cases hx : x ∈ timeSlab T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ (hsub hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [e]
  exact hpw.indicator (measurableSet_timeSlab T)

end RegularityStructures

end
