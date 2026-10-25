/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.MainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Local.MainWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.WrapG
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The local and layer bounds for scaled test functions, near-pair `Γ`-bounds

For `g` scaled at `x` with radius `R` and constant `A`, vanishing after time `T`: the local bound
[Hai14, (6.6)] `|⟨R f, g⟩ - ⟨Π_x f(x), g⟩| ≤ C K₀ C_f (A R⁵) R^γ ‖x‖_P^{η-γ}` when `64 R ≤ ‖x‖_P`
and `T ≤ 1` (`exists_abs_latticeRecon_sub_pairing_le_of_scaled_win_near`), and the layer bound
[Hai14, Proposition 6.9] `|⟨R f, g⟩| ≤ C K₀ C_f (A R⁵) R^{α ∧ η}`
(`exists_abs_latticeRecon_le_of_scaled_win_near`). The qualitative growth model of the setting
enters only identities and convergence, never the constant `C`.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- **Local bound for scaled test functions** [Hai14, (6.6)], window models: for `g` scaled at
`x` with radius `R` and constant `A`, `64 R ≤ ‖x‖_P`, vanishing after time `T ≤ 1`,
`|⟨R f, g⟩ - ⟨Π_x f(x), g⟩| ≤ C K₀ C_f (A R⁵) R^γ ‖x‖_P^{η-γ}`. -/
theorem exists_abs_latticeRecon_sub_pairing_le_of_scaled_win_near (𝒯 : RegularityStructure ι)
    {γ : ℝ} (η : ℝ) (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ}
      {g : ParabolicSpace → ℝ} {x : ParabolicSpace} {R A : ℝ},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 → (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f →
      IsScaledTest g x R A → x ∈ timeSlab T → 64 * R ≤ singularWeight timeZeroDist x →
      (∀ w : ParabolicSpace, T < w.1 → g w = 0) →
      Tendsto (M.latticeApprox f g) atTop (𝓝 (M.latticeRecon f g)) ∧
      |M.latticeRecon f g - parabolicSemigroup.pairing (M.regPi x (f x)) g| ≤
        C * (max 1 CGam * CPi) * Cf * ((A * R ^ 5) * R ^ γ) *
          singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨C, hC0, hC⟩ := exists_tendsto_and_abs_latticeRecon_sub_pairing_le_win_near 𝒯 η hγ hdeg
  refine ⟨C, hC0, fun M CPi CGam Cf f T g x R A hPi hCPi hGam hgrowth hT1 hfT hf hg hx hxw hgT =>
    ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  obtain ⟨φ, hφ, hgeq⟩ := hg.exists_eq_smul
  have hc : 0 < A * R ^ 5 := mul_pos hg.const_pos (pow_pos hg.radius_pos 5)
  have hψT : ∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ R x w = 0 := by
    intro w hw
    have := hgT w hw
    rw [hgeq] at this
    simpa [hc.ne'] using this
  obtain ⟨hT, hb⟩ := hC M hPi hCPi hGam ⟨_, _, _, _, _, _, G⟩ hT1 hfT hf hφ hg.radius_pos
    hg.radius_le_one hx hxw hψT
  obtain ⟨h1, h2⟩ := M.tendsto_latticeApprox_smul_rescaled_growth G hdeg hfT hφ hg.radius_pos
    hT (A * R ^ 5)
  have hp := M.pairing_regPi_smul_of_scaled_growth G hdeg (hfT x) hg hc.ne' hgeq
  rw [← hgeq] at h1 h2
  refine ⟨h1, ?_⟩
  rw [hp, h2, ← mul_sub, abs_mul, abs_of_pos hc]
  calc _ ≤ (A * R ^ 5) * (C * (max 1 CGam * CPi) * Cf * R ^ γ *
        singularWeight timeZeroDist x ^ (η - γ)) := mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by ring

/-- **Layer bound for scaled test functions** (Hairer, Prop. 6.9), window models: for `g` scaled
at `x` with radius `R` and constant `A`, vanishing after time `T`,
`|⟨R f, g⟩| ≤ C K₀ C_f (A R⁵) R^{α ∧ η}`. -/
theorem exists_abs_latticeRecon_le_of_scaled_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {g : ParabolicSpace → ℝ} {x : ParabolicSpace} {R A : ℝ}, IsScaledTest g x R A →
      (∀ w : ParabolicSpace, T < w.1 → g w = 0) →
      Tendsto (M.latticeApprox f g) atTop (𝓝 (M.latticeRecon f g)) ∧
      |M.latticeRecon f g| ≤
        C * (max 1 CGam * CPi) * Cf * ((A * R ^ 5) * R ^ (min α η)) := by
  obtain ⟨C, hC0, hC⟩ := exists_tendsto_latticeApprox_abs_latticeRecon_le_win_near 𝒯 γ η α
    hdeg hγ hαγ hαη
  refine ⟨C, hC0, fun M f T Cf CPi CGam S g x R A hg hgT => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  obtain ⟨φ, hφ, hgeq⟩ := hg.exists_eq_smul
  have hc : 0 < A * R ^ 5 := mul_pos hg.const_pos (pow_pos hg.radius_pos 5)
  have hψT : ∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ R x w = 0 := by
    intro w hw
    have := hgT w hw
    rw [hgeq] at this
    simpa [hc.ne'] using this
  obtain ⟨hT, hb⟩ := hC M f T Cf CPi CGam S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf S.hf0 S.hα
    S.hCf hφ hg.radius_pos hg.radius_le_one x hψT
  obtain ⟨h1, h2⟩ := M.tendsto_latticeApprox_smul_rescaled_growth G S.hdeg S.hfT hφ
    hg.radius_pos hT (A * R ^ 5)
  rw [← hgeq] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, abs_mul, abs_of_pos hc]
  calc _ ≤ (A * R ^ 5) * (C * (max 1 CGam * CPi) * Cf * R ^ (min α η)) :=
        mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by ring

end Model

end RegularityStructures

end
