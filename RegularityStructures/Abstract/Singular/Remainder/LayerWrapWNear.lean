/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.MainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.Kernel.LinearW
public import RegularityStructures.Abstract.Singular.Kernel.Vanish
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The layer bound for a smooth function supported in a unit ball, near-pair `Γ`-bounds

`exists_abs_latticeRecon_le_of_unit_ball_win_near`: a smooth `g` supported in `B(z, 1)`, vanishing
after time `T`, with derivatives of order `≤ 4` (in the coordinates `v ↦ g(z + v)`) bounded by
`A ≥ 0`, has convergent lattice approximations and `|⟨R f, g⟩| ≤ C K₀ Cf A`.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Filter Topology Set

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_latticeRecon_le_of_unit_ball_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {A : ℝ}, ContDiff ℝ ∞ g → 0 ≤ A →
      (∀ w, 1 < parabolicNorm (w - z) → g w = 0) →
      (∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (fun v => g (z + v)) v‖ ≤ A) →
      (∀ w : ParabolicSpace, T < w.1 → g w = 0) →
      Tendsto (M.latticeApprox f g) atTop (𝓝 (M.latticeRecon f g)) ∧
        |M.latticeRecon f g| ≤ C * (max 1 CGam * CPi) * Cf * A := by
  obtain ⟨C, hC0, hC⟩ := exists_tendsto_latticeApprox_abs_latticeRecon_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  refine ⟨C, hC0, fun M f T Cf CPi CGam S g z A hg hA hsupp hder hT => ?_⟩
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `g = 0`
    have hg0 : g = fun _ => 0 := by
      funext w
      have := hder 0 (by norm_num) (w - z)
      rw [← hA0, norm_iteratedFDeriv_zero] at this
      have h3 : ‖g w‖ ≤ 0 := by simpa using this
      exact norm_le_zero_iff.1 h3
    have hz : ∀ n, M.latticeApprox f g n = 0 := fun n =>
      M.latticeApprox_eq_zero_of_causal (fun w _ => by rw [hg0]) (fun z hz => S.hf0 z
        (fun h => absurd h.1 (not_lt.2 hz))) n
    have hr : M.latticeRecon f g = 0 :=
      M.latticeRecon_eq_zero_of_causal (fun w _ => by rw [hg0])
        (fun z hz => S.hf0 z (fun h => absurd h.1 (not_lt.2 hz)))
    refine ⟨?_, ?_⟩
    · have : M.latticeApprox f g = fun _ => 0 := funext hz
      rw [hr, this]; exact tendsto_const_nhds
    · rw [hr, ← hA0]; simp
  · have hsc : IsScaledTest g z 1 A := ⟨hg, one_pos, le_rfl, hApos, hsupp, by
      intro k hk v; simpa [parabolicDilate_one] using hder k hk v⟩
    obtain ⟨φ, hφ, hgeq⟩ := hsc.exists_eq_smul
    set c : ℝ := A * 1 ^ 5 with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    set φ' := rescaledTestFunction φ 1 z with hφ'
    have hφg : φ' = c⁻¹ • g := by
      rw [hgeq, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
    have hφT : ∀ w : ParabolicSpace, T < w.1 → φ' w = 0 := fun w hw => by
      rw [hφg]; simp [hT w hw]
    obtain ⟨hlim, hb⟩ := hC M f T Cf CPi CGam S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf S.hf0 S.hα S.hCf hφ
      one_pos le_rfl z hφT
    have hψ : ContDiff ℝ ∞ φ' := by rw [hφg]; exact contDiff_const.smul hg
    have hs : ∀ w, 1 < parabolicNorm (w - z) → φ' w = 0 := fun w hw => by
      rw [hφg]; simp [hsupp w hw]
    have hgc : g = c • φ' := hgeq
    refine ⟨?_, ?_⟩
    · have := M.tendsto_latticeApprox_smul_win S.hfT S.hgrowth S.hdeg hψ hs c hlim
      rw [hgc, M.latticeRecon_smul_win S.hfT S.hgrowth S.hdeg hψ hs c hlim]
      exact this
    · rw [hgc, M.latticeRecon_smul_win S.hfT S.hgrowth S.hdeg hψ hs c hlim, abs_mul,
        abs_of_pos hcpos]
      have h1 : |M.latticeRecon f φ'| ≤ C * (max 1 CGam * CPi) * Cf := by
        simpa using hb
      calc c * |M.latticeRecon f φ'| ≤ A * (C * (max 1 CGam * CPi) * Cf) := by
            rw [hc]; simp only [one_pow, mul_one]
            exact mul_le_mul_of_nonneg_left h1 hA
        _ = _ := by ring

end RegularityStructures

end
