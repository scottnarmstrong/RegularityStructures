/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.MeasReconWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.MeasPairingG

/-!
# Measurability of the singular `𝒦_γ f` on the time slab, near-pair `Γ`-bounds

Under joint measurability of the model, measurability of `f`, causality of the profile, and
summability of the shell series for the multi-indices `|k|_𝔰 < γ + 2`, the restriction
`x ↦ 1_{timeSlab T}(x) · 𝒦_γ f(x)` is measurable (`measurable_indicator_kGammaS_of_lt_win_near`).
The coefficients `N_k` are treated one index at a time
(`measurable_indicator_nCoeffS_of_lt_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N N' : ℕ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem measurable_indicator_singShellPairing_win_near (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (hfm : Measurable f) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Measurable ((timeSlab T).indicator fun x => M.singShellPairing h f x k n) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have e : (timeSlab T).indicator (fun x => M.singShellPairing h f x k n) = fun x =>
      (timeSlab T).indicator (fun x => M.latticeRecon f
        (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))) x -
      (timeSlab T).indicator (fun x => parabolicSemigroup.pairing (M.regPi x (f x))
        (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))) x := by
    funext x
    by_cases hx : x ∈ timeSlab T <;> simp [Set.indicator, hx, singShellPairing]
  rw [e]
  exact (M.measurable_indicator_latticeRecon_lineIter_win_near hh hc S k n (measurableSet_timeSlab T)
    fun x hx => hx.2).sub
    ((M.measurable_pairing_regPi_apply_lineIter_growth hJ hh G S.hdeg hfm S.hfT k
      n).indicator (measurableSet_timeSlab T))

/-- Measurability of the coefficient `N_k`, with summability at the single index `k`. -/
theorem measurable_indicator_nCoeffS_of_lt_win_near (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (hfm : Measurable f)
    (k : Fin 4 →₀ ℕ)
    (hS : ∀ x ∈ timeSlab T, Summable (M.singShellPairing h f x k)) :
    Measurable ((timeSlab T).indicator fun x => M.nCoeffS h f x k) := by
  have e : (timeSlab T).indicator (fun x => M.nCoeffS h f x k) = fun x =>
      ∑' n, (timeSlab T).indicator (fun x => M.singShellPairing h f x k n) x := by
    funext x
    by_cases hx : x ∈ timeSlab T
    · simp [Set.indicator_of_mem hx, nCoeffS]
    · simp [Set.indicator_of_notMem hx]
  rw [e]
  refine measurable_tsum_of_summable
    (fun n => M.measurable_indicator_singShellPairing_win_near hJ hh hc S hfm k n) fun x => ?_
  by_cases hx : x ∈ timeSlab T
  · simpa [Set.indicator_of_mem hx] using hS x hx
  · simp [Set.indicator_of_notMem hx]

/-- **Measurability of the singular `𝒦_γ f` on the time slab**, with summability of the shell
series needed only for the multi-indices `|k|_𝔰 < γ + 2`. -/
theorem measurable_indicator_kGammaS_of_lt_win_near (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (hfm : Measurable f)
    (hS : ∀ x ∈ timeSlab T, ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      Summable (M.singShellPairing h f x k))
    {P : PolynomialSector 𝒯 N'} (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    Measurable ((timeSlab T).indicator fun x => M.kGammaS h P I γ f x) := by
  classical
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hSm := measurableSet_timeSlab T
  have hI : Measurable fun x => I (f x) :=
    (LinearMap.continuous_of_finiteDimensional I).measurable.comp hfm
  have hj : Measurable fun x => jMapP M h P x (f x) :=
    M.measurable_jMapP_apply_growth hJ hh G S.hdeg hfm S.hfT
  have hn : Measurable ((timeSlab T).indicator fun x => M.nVecS h P γ f x) := by
    have e : (timeSlab T).indicator (fun x => M.nVecS h P γ f x) = fun x =>
        ∑ k : PolyIndex N', if polyDeg N' k < γ + 2 then
          (((timeSlab T).indicator (fun x => M.nCoeffS h f x k.1) x) / multiFactorial k.1) •
            (Pi.single (P.emb k) 1 : ι → ℝ) else 0 := by
      funext x
      by_cases hx : x ∈ timeSlab T
      · simp only [Set.indicator_of_mem hx]
        rfl
      · simp [Set.indicator_of_notMem hx]
    rw [e]
    refine Finset.measurable_sum _ fun k _ => ?_
    split_ifs with hk
    · exact (((M.measurable_indicator_nCoeffS_of_lt_win_near hJ hh hc S hfm k.1
      fun x hx => hS x hx k.1 hk).div_const _)).smul_const _
    · exact measurable_const
  have e : (timeSlab T).indicator (fun x => M.kGammaS h P I γ f x) = fun x =>
      (timeSlab T).indicator (fun x => I (f x)) x +
        (timeSlab T).indicator (fun x => jMapP M h P x (f x)) x +
        (timeSlab T).indicator (fun x => M.nVecS h P γ f x) x := by
    funext x
    by_cases hx : x ∈ timeSlab T
    · simp [Set.indicator_of_mem hx, kGammaS]
    · simp [Set.indicator_of_notMem hx]
  rw [e]
  exact ((hI.indicator hSm).add (hj.indicator hSm)).add hn

end Model

end RegularityStructures

end
