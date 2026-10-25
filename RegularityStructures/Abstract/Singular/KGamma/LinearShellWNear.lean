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
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.LinearApproxG
public import RegularityStructures.Abstract.Singular.Kernel.Shell

/-!
# Linearity of the shell pairings in `f`, near-pair `Γ`-bounds

For `x` in the time slab and a causal shell profile, the shell pairing
`⟨R f, D^k K_n(x − ·)⟩ − ⟨Π_x f(x), D^k K_n(x − ·)⟩` (`singShellPairing`) is additive and
homogeneous in `f` (`singShellPairing_add_win_near`, `singShellPairing_smul_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ}
  {γ η α C₁ C₂ CPi CGam T : ℝ} {f f₁ f₂ : ParabolicSpace → ι → ℝ}

theorem singShellPairing_add_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (k : Fin 4 →₀ ℕ) (n : ℕ) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.singShellPairing h (f₁ + f₂) x k n =
      M.singShellPairing h f₁ x k n + M.singShellPairing h f₂ x k n := by
  obtain ⟨_, _, _, _, _, _, G₁⟩ := S₁.hgrowth
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  have hg := hC n x
  have t₁ := M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S₁ k n hx.2
  have t₂ := M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S₂ k n hx.2
  obtain ⟨-, hrec⟩ := M.latticeRecon_add_fun_growth S₁.hfT S₂.hfT G₁ S₁.hdeg
    hg.contDiff hg.supp t₁ t₂
  unfold singShellPairing
  rw [hrec, Pi.add_apply,
    M.pairing_regPi_add_of_scaled_growth G₁ S₁.hdeg (S₁.hfT x) (S₂.hfT x) hg]
  ring

theorem singShellPairing_smul_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ)
    (k : Fin 4 →₀ ℕ) (n : ℕ) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.singShellPairing h (c • f) x k n = c * M.singShellPairing h f x k n := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  have hg := hC n x
  have t := M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S k n hx.2
  obtain ⟨-, hrec⟩ := M.latticeRecon_smul_fun_growth S.hfT G S.hdeg c
    hg.contDiff hg.supp t
  unfold singShellPairing
  rw [hrec, Pi.smul_apply,
    M.pairing_regPi_const_smul_of_scaled_growth G S.hdeg (S.hfT x) c hg]
  ring

end Model

end RegularityStructures

end
