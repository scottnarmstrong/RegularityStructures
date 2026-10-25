/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.WindowAt.ScaledNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.SeriesTaylor
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Taylor-kernel bounds for the reconstruction, near-pair `Γ`-bounds

Bounds on the pairings of `R f`, of `R f − Π_x f(x)` and of `Π_x e_i` with the Taylor kernels
`K^{k,σ}_{n;yx}` at scales `n ≥ 1`, together with the single-vector bound
`|⟨Π_z e_i, g⟩| ≤ c K₀ (A R⁵) R^{deg i}` for test functions scaled at slab base points, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

namespace Model

variable {h : ParabolicSpace → ℝ}

/-- Window form of the single-vector bound: for `g` scaled at a slab base point `z`
(`0 ≤ z₀ ≤ 1`), `|⟨Π_z e_i, g⟩| ≤ c K₀ (A R⁵) R^{deg i}`. -/
theorem abs_pairing_regPi_single_le_of_scaled_slabAt_win_near {M : Model 𝒯 parabolicSemigroup}
    {γ CPi CGam : ℝ} (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    {z : ParabolicSpace} (hgrowth : M.HasQualitativeGrowthAt γ z)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ)
    {g : ParabolicSpace → ℝ} {R A : ℝ} (hg : IsScaledTest g z R A)
    (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) * R ^ 𝒯.deg i :=
  (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam hgrowth hdeg hi
    (fun _ hy => ball_subset_hairerTimeWindow hz0 hz1 hy) hg).2

/-- **Local bound for the Taylor kernel**, scales `n ≥ 1`, window models: for
`128 · 2^{-n} ≤ ‖x‖_P`,
`|⟨R f − Π_x f(x), K^{k,σ}_{n;yx}⟩| ≤ C K₀ C_f d^σ (2^n)^{σ + |k| − 2 − γ} ‖x‖_P^{η−γ}`. -/
theorem exists_abs_latticeRecon_sub_pairing_dTaylor_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ}
      {x y : ParabolicSpace} (n : ℕ), 1 ≤ n →
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 → (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f → x ∈ timeSlab T → y.1 ≤ T →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      128 * ((2 : ℝ) ^ n)⁻¹ ≤ singularWeight timeZeroDist x →
      |M.latticeRecon f (dTaylorKernel h k n σ x y) -
          parabolicSemigroup.pairing (M.regPi x (f x)) (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) * singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_sub_pairing_le_of_scaled_win_near 𝒯 η hγ hdeg
  obtain ⟨Cd, hCd, H⟩ := exists_isScaledTest_dTaylorKernel hh k hσ
  refine ⟨Cl * (Cd * 2 ^ 5 * 2 ^ γ), by positivity,
    fun M {CPi CGam Cf f T x y} n hn hPi hCPi hGam hgrowth hT1 hfT hf hx hy hd hdn hw => ?_⟩
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hg := H n hn x y hd hdn
  obtain ⟨_, hb⟩ := hCl M hPi hCPi hGam hgrowth hT1 hfT hf hg hx (by linarith)
    (fun w hw => dTaylorKernel_eq_zero_of_lt hh.contDiff hc k n σ hx.2 hy w hw)
  refine hb.trans (le_of_eq ?_)
  have e := taylor_scale_eq hu hd Cd σ (multiDeg k) γ
  linear_combination (Cl * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (η - γ)) * e

/-- **Layer bound for the Taylor kernel**, scales `n ≥ 1`, window models:
`|⟨R f, K^{k,σ}_{n;yx}⟩| ≤ C K₀ C_f d^σ (2^n)^{σ + |k| − 2 − α ∧ η}`. -/
theorem exists_abs_latticeRecon_dTaylor_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ)
    (𝒯 : RegularityStructure ι) (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hγ : 0 < γ) (hαγ : α ≤ γ) (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace} (n : ℕ), 1 ≤ n → x.1 ≤ T → y.1 ≤ T →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      |M.latticeRecon f (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - min α η)) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_scaled_win_near 𝒯 γ η α hdeg hγ hαγ
    hαη
  obtain ⟨Cd, hCd, H⟩ := exists_isScaledTest_dTaylorKernel hh k hσ
  refine ⟨Cl * (Cd * 2 ^ 5 * 2 ^ (min α η)), by positivity,
    fun M f T Cf CPi CGam S x y n hn hx hy hd hdn => ?_⟩
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hg := H n hn x y hd hdn
  obtain ⟨_, hb⟩ := hCl M f T Cf CPi CGam S hg
    (fun w hw => dTaylorKernel_eq_zero_of_lt hh.contDiff hc k n σ hx hy w hw)
  refine hb.trans (le_of_eq ?_)
  have e := taylor_scale_eq hu hd Cd σ (multiDeg k) (min α η)
  linear_combination (Cl * (max 1 CGam * CPi) * Cf) * e

/-- `|⟨Π_x e_i, K^{k,σ}_{n;yx}⟩| ≤ C K₀ d^σ (2^n)^{σ + |k| − 2 − deg i}`, scales `n ≥ 1`,
for `x` with `0 ≤ x₀ ≤ 1` (window models). -/
theorem exists_abs_pairing_dTaylor_le_win_near (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ}
    (hσ : 0 < σ) (𝒯 : RegularityStructure ι) {γ : ℝ}  
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      {x y : ParabolicSpace} (n : ℕ) (i : ι), 1 ≤ n →
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      0 ≤ x.1 → x.1 ≤ 1 → 𝒯.deg i < γ →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i)) := by
  obtain ⟨Cd, hCd, H⟩ := exists_isScaledTest_dTaylorKernel hh k hσ
  have hr := r4ModelConst_nonneg 𝒯 hdeg
  refine ⟨r4ModelConst 𝒯 γ * (Cd * 2 ^ 5 * ∑ j : ι, (2 : ℝ) ^ 𝒯.deg j),
    by positivity, fun M {CPi CGam x y} n i hn hPi hCPi hGam hgrowth hx0 hx1 hi hd hdn => ?_⟩
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hg := H n hn x y hd hdn
  have hb := abs_pairing_regPi_single_le_of_scaled_slabAt_win_near hPi hCPi hGam
    (M.hasQualitativeGrowthAt_of_exists hgrowth x) hdeg hi hg hx0 hx1
  have e := taylor_scale_eq hu hd Cd σ (multiDeg k) (𝒯.deg i)
  have hK : 0 ≤ max 1 CGam * CPi :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  have hX : 0 ≤ (max 1 CGam * CPi) * (parabolicNorm (y - x) ^ σ *
      ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i)) := by
    have := parabolicNorm_nonneg (y - x)
    positivity
  have hsum : (2 : ℝ) ^ 𝒯.deg i ≤ ∑ j : ι, (2 : ℝ) ^ 𝒯.deg j :=
    Finset.single_le_sum (f := fun j : ι => (2 : ℝ) ^ 𝒯.deg j) (fun j _ => by positivity)
      (Finset.mem_univ i)
  refine hb.trans ?_
  calc _ = (r4ModelConst 𝒯 γ * (Cd * 2 ^ 5 * 2 ^ 𝒯.deg i)) *
        ((max 1 CGam * CPi) *
        (parabolicNorm (y - x) ^ σ * ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i))) := by
        linear_combination (r4ModelConst 𝒯 γ * (max 1 CGam * CPi)) * e
    _ ≤ (r4ModelConst 𝒯 γ * (Cd * 2 ^ 5 * ∑ j : ι, (2 : ℝ) ^ 𝒯.deg j)) *
        ((max 1 CGam * CPi) *
        (parabolicNorm (y - x) ^ σ * ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i))) := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hr
    _ = _ := by ring

end Model

end RegularityStructures

end
