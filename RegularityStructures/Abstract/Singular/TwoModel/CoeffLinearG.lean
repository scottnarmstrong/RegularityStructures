/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.RealGermG
public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The `J`-coefficients and germs of the difference model, under weighted bounds

Weighted versions of `jCoeffP_modelSum_inl`, `realGermP_modelSum_inl`
(`RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear`): the global bounds `PiBoundOn`,
`GammaBoundOn` are replaced by `Model.GrowthModel` (`M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG`,
`M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG`). The non-integrality hypothesis `hnat` of the unweighted
germ identity is not needed here. The `inr` identities `jCoeffP_modelSum_inr`,
`realGermP_modelSum_inr` do not involve bounds.

* `Model.GrowthModel.integrable_regPi_single_mul_of_hasCompactSupport`;
* `jCoeffP_modelSum_inl_growth`: `jCoeffP M⊕ h x (inl j) k = λ⁻¹ (jCoeffP M₁ h x j k - jCoeffP M₂ h x j k)`;
* `realGermP_modelSum_inl_growth`: the same for the germs.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem Model.GrowthModel.integrable_regPi_single_mul_of_hasCompactSupport
    {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x : ParabolicSpace) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) {φ : ParabolicSpace → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable fun z => M.regPi x (Pi.single i 1) s z * φ z := by
  have hloc := G.localGrowth_regPi hV hVb hdeg hVi hi x
  exact integrable_mul_of_hasCompactSupport_growth hloc.mem hloc.meas hloc.nonneg
    hloc.nonneg_exp (fun a ha => (hloc.exps a ha).2) hloc.loc hs hφ hc

namespace TwoModel

variable {N' : ℕ} {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}
  {γ CPi₁ CGam₁ CPi₂ CGam₂ p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

theorem jCoeffP_modelSum_inl_growth (hh : ShellProfile h N) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) (j : NonPoly P)
    (hVj : (Pi.single j.1 1 : ι → ℝ) ∈ V) (hj : 𝒯.deg j.1 < γ)
    (x : ParabolicSpace) {k : Fin 4 →₀ ℕ} (hk : (multiDeg k : ℝ) < 𝒯.deg j.1 + 2) :
    jCoeffP (modelSum (lam := lam) h₁ h₂) h x (Sum.inl j) k =
      lam⁻¹ * (jCoeffP M₁ h x j.1 k - jCoeffP M₂ h x j.1 k) := by
  have hl₁ := G₁.localGrowth_regPi hV hVb hdeg hVj hj x
  have hl₂ := G₂.localGrowth_regPi hV hVb hdeg hVj hj x
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing
      (fun t y => (modelSum (lam := lam) h₁ h₂).regPi x (Pi.single (Sum.inl j) 1) t y)
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) =
      lam⁻¹ * (parabolicSemigroup.pairing (fun t y => M₁.regPi x (Pi.single j.1 1) t y)
        (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) -
        parabolicSemigroup.pairing (fun t y => M₂.regPi x (Pi.single j.1 1) t y)
        (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))) := by
    intro n
    have hg := contDiff_scaledShell hh.contDiff n
    have hφ : Continuous fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) :=
      (contDiff_lineIter hg _).continuous.comp (continuous_const.sub continuous_id)
    have hφc : HasCompactSupport fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) :=
      hasCompactSupport_reflect (hasCompactSupport_lineIter
        (hasCompactSupport_scaledShell hh.eq_zero n) _) x
    exact pairing_modelSum_inl h₁ h₂ j x
      (fun s hs => G₁.integrable_regPi_single_mul_of_hasCompactSupport hV hVb hdeg hVj hj x hs
        hφ hφc)
      (fun s hs => G₂.integrable_regPi_single_mul_of_hasCompactSupport hV hVb hdeg hVj hj x hs
        hφ hφc)
      (tendsto_dShell_centre_growth hl₁.mem hl₁.meas hh.contDiff hh.eq_zero hl₁.exps hl₁.nonneg
        hl₁.nonneg_exp hl₁.loc k n)
      (tendsto_dShell_centre_growth hl₂.mem hl₂.meas hh.contDiff hh.eq_zero hl₂.exps hl₂.nonneg
        hl₂.nonneg_exp hl₂.loc k n)
  have s₁ := summable_jCoeff_terms_growthP M₁ hh G₁ x j.1 k hV hVb hVj hj hdeg hk
  have s₂ := summable_jCoeff_terms_growthP M₂ hh G₂ x j.1 k hV hVb hVj hj hdeg hk
  unfold jCoeffP
  rw [tsum_congr hterm, tsum_mul_left, Summable.tsum_sub s₁ s₂]

theorem realGermP_modelSum_inl_growth (hh : ShellProfile h N) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) (j : NonPoly P)
    (hVj : (Pi.single j.1 1 : ι → ℝ) ∈ V) (hj : 𝒯.deg j.1 < γ) (x y : ParabolicSpace) :
    realGermP (modelSum (lam := lam) h₁ h₂) h x (Sum.inl j) y =
      lam⁻¹ * (realGermP M₁ h x j.1 y - realGermP M₂ h x j.1 y) := by
  have hdeg4 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j :=
    fun j hjV hj => by linarith [hdeg j hjV hj]
  have hl₁ := G₁.localGrowth_regPi hV hVb hdeg4 hVj hj x
  have hl₂ := G₂.localGrowth_regPi hV hVb hdeg4 hVj hj x
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing
      (fun t z => (modelSum (lam := lam) h₁ h₂).regPi x (Pi.single (Sum.inl j) 1) t z)
      (taylorKernel h n (𝒯.deg j.1 + 2) x y) =
      lam⁻¹ * (parabolicSemigroup.pairing (fun t z => M₁.regPi x (Pi.single j.1 1) t z)
        (taylorKernel h n (𝒯.deg j.1 + 2) x y) -
        parabolicSemigroup.pairing (fun t z => M₂.regPi x (Pi.single j.1 1) t z)
        (taylorKernel h n (𝒯.deg j.1 + 2) x y)) := fun n =>
    pairing_modelSum_inl h₁ h₂ j x
      (fun s hs => G₁.integrable_regPi_single_mul_of_hasCompactSupport hV hVb hdeg4 hVj hj x hs
        (continuous_taylorKernel_right hh.contDiff n _ x y)
        (hasCompactSupport_taylorKernel hh.contDiff hh.eq_zero n _ x y))
      (fun s hs => G₂.integrable_regPi_single_mul_of_hasCompactSupport hV hVb hdeg4 hVj hj x hs
        (continuous_taylorKernel_right hh.contDiff n _ x y)
        (hasCompactSupport_taylorKernel hh.contDiff hh.eq_zero n _ x y))
      (tendsto_integral_taylorKernel_growth hl₁.mem hl₁.meas hh.contDiff hh.eq_zero
        (fun a ha => hl₁.exps a ha) hl₁.nonneg hl₁.nonneg_exp hl₁.loc _ n)
      (tendsto_integral_taylorKernel_growth hl₂.mem hl₂.meas hh.contDiff hh.eq_zero
        (fun a ha => hl₂.exps a ha) hl₂.nonneg hl₂.nonneg_exp hl₂.loc _ n)
  have s₁ := M₁.summable_pairing_taylorKernel_growthP hh G₁ hV hVb hdeg hVj hj x y
  have s₂ := M₂.summable_pairing_taylorKernel_growthP hh G₂ hV hVb hdeg hVj hj x y
  unfold realGermP
  refine (tsum_congr hterm).trans ?_
  rw [tsum_mul_left, Summable.tsum_sub s₁ s₂]

end TwoModel

end RegularityStructures

end
