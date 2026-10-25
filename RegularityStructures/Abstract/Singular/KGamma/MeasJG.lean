/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Singular.KGamma.SupCoeffG
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.Kernel.Shell

/-!
# Measurability of the profile-generic `J`-map in the base point, weighted models

Weighted (`_growth`) version: only qualitative growth (`Model.GrowthModel`) is
needed for convergence of the shell series.

For a general shell profile, under `Model.IsJointMeasurable`, the maps `x ↦ jCoeffP M h x i k`,
`x ↦ jVecP M h P x i` and, for a measurable `f` with values in `T_{<γ}`, `x ↦ jMapP M h P x (f x)`
are measurable.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ}
  {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ} {P : PolynomialSector 𝒯 N'}

/-- Each term `⟨Π_x e_i, D^k K_n(x − ·)⟩` of `jCoeffP` is measurable in `x`. -/
theorem measurable_derivShellPairing_regPi_single_growth (hJ : M.IsJointMeasurable)
    (hh : ShellProfile h N) (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {i : ι} (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Measurable fun x => derivShellPairing (fun t y => M.regPi x (Pi.single i 1) t y) h k x n := by
  obtain ⟨C, -, hCs⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  have hτ : (Pi.single i 1 : ι → ℝ) ∈ lowerSubspace 𝒯.deg γ := by
    refine (mem_lowerSubspace).2 fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact absurd hi (not_lt.2 hj)
    · simp [hji]
  have hg : ContDiff ℝ ∞ (lineIter (multiDirs k) (scaledShell h n)) :=
    contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _
  have hF : ∀ m : ℕ, Measurable fun x => ∫ z, M.regPi x (Pi.single i 1) (1 / ((m : ℝ) + 1)) z *
      lineIter (multiDirs k) (scaledShell h n) (x - z) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        M.regPi p.1 (Pi.single i 1) (1 / ((m : ℝ) + 1)) p.2 *
          lineIter (multiDirs k) (scaledShell h n) (p.1 - p.2) :=
      (hJ i _ hpos).mul (hg.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun x => ?_)
  have key := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg hτ (hCs n x)
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  exact key.comp hseq

theorem measurable_jCoeffP_growth (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {i : ι} (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {k : Fin 4 →₀ ℕ}
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    Measurable fun x => jCoeffP M h x i k :=
  measurable_tsum_of_summable
    (fun n => measurable_derivShellPairing_regPi_single_growth hJ hh G hi hdeg k n)
    fun x => summable_jCoeffTermsP_of_growth M hh x i k G hi hdeg hk

theorem measurable_jVecP_growth (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {i : ι} (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    Measurable fun x => jVecP M h P x i := by
  unfold jVecP
  refine Finset.measurable_sum _ fun k _ => ?_
  split_ifs with hc
  · exact ((measurable_jCoeffP_growth hJ hh G hi hdeg hc).div_const _).smul_const _
  · exact measurable_const

/-- Measurability of `x ↦ J(x) f(x)` for the profile-generic `J`. -/
theorem measurable_jMapP_apply_growth (hJ : M.IsJointMeasurable) (hh : ShellProfile h N)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {f : ParabolicSpace → ι → ℝ}
    (hfm : Measurable f) (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) :
    Measurable fun x => jMapP M h P x (f x) := by
  have e : (fun x => jMapP M h P x (f x)) = fun x => ∑ i, f x i • jVecP M h P x i := rfl
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hi : 𝒯.deg i < γ
  · exact ((measurable_pi_apply i).comp hfm).smul (measurable_jVecP_growth hJ hh G hi hdeg)
  · have h0 : (fun x => f x i • jVecP M h P x i) = fun _ => 0 :=
      funext fun x => by rw [(mem_lowerSubspace).1 (hfT x) i (not_lt.1 hi), zero_smul]
    rw [h0]
    exact measurable_const

end Model

end RegularityStructures

end
