/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapWNear
public import RegularityStructures.Abstract.Singular.Layer.MainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.MeasReconG
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Convergence and measurability of the shell pairings of `R f`, near-pair `Γ`-bounds

For `x₀ ≤ T`, the lattice approximations of `f` against the shell derivative `D^k K_n(x − ·)`
converge to its lattice reconstruction (layer bound plus causality), and `x ↦ ⟨R f, D^k K_n(x − ·)⟩`
is measurable on every measurable subset of `{x₀ ≤ T}`, for models whose `Γ`-bounds hold only for
near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set Filter

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam : ℝ}

variable {h : ParabolicSpace → ℝ} {N : ℕ} {η α Cf T : ℝ}

/-- For `x₀ ≤ T`, the lattice approximations of the shell derivative `D^k K_n(x − ·)` converge to
`latticeRecon` (layer bound plus causality). -/
theorem tendsto_latticeApprox_lineIter_scaledShell_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (k : Fin 4 →₀ ℕ) (n : ℕ) {x : ParabolicSpace}
    (hx : x.1 ≤ T) :
    Tendsto (M.latticeApprox f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)))
      atTop (𝓝 (M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)))) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  obtain ⟨Cl, -, hL⟩ := exists_tendsto_latticeApprox_abs_latticeRecon_le_win_near 𝒯 γ η α S.hdeg S.hγ
    S.hαγ S.hαη
  have hg := hC n x
  set g : ParabolicSpace → ℝ := fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) with hgdef
  obtain ⟨φ, hφ, heq⟩ := hg.exists_eq_smul
  set c : ℝ := C * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) *
    (((2 : ℝ) ^ n)⁻¹) ^ 5 with hcdef
  have hcpos : 0 < c := mul_pos hg.const_pos (pow_pos hg.radius_pos 5)
  have hres : rescaledTestFunction φ (((2 : ℝ) ^ n)⁻¹) x = c⁻¹ • g := by
    rw [heq]
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hvan : ∀ w : ParabolicSpace, T < w.1 →
      rescaledTestFunction φ (((2 : ℝ) ^ n)⁻¹) x w = 0 := fun w hw => by
    rw [hres]
    simp only [Pi.smul_apply, smul_eq_mul, hgdef]
    rw [lineIter_multiDirs_scaledShell_sub_eq_zero hh.contDiff hc k n (hx.trans hw.le), mul_zero]
  have hlayer := (hL M f T Cf CPi CGam S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf S.hf0 S.hα S.hCf hφ
    hg.radius_pos hg.radius_le_one x hvan).1
  rw [hres] at hlayer
  set L := M.latticeRecon f (c⁻¹ • g) with hLdef
  have h1 : Tendsto (fun m => c⁻¹ * M.latticeApprox f g m) atTop (𝓝 L) := by
    refine hlayer.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with m hm
    exact M.latticeApprox_smul_growth S.hfT G S.hdeg hg.contDiff hg.supp c⁻¹ hm
  have h2 : Tendsto (M.latticeApprox f g) atTop (𝓝 (c * L)) := by
    refine (h1.const_mul c).congr fun m => ?_
    rw [mul_inv_cancel_left₀ hcpos.ne']
  have h3 : M.latticeRecon f g = c * L := h2.limUnder_eq
  rw [h3]
  exact h2

/-- `x ↦ ⟨R f, D^k K_n(x − ·)⟩` is measurable on every measurable subset `A` of `{x₀ ≤ T}`. -/
theorem measurable_indicator_latticeRecon_lineIter_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (k : Fin 4 →₀ ℕ) (n : ℕ)
    {A : Set ParabolicSpace} (hA : MeasurableSet A) (hAT : ∀ x ∈ A, x.1 ≤ T) :
    Measurable (A.indicator fun x =>
      M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))) := by
  obtain ⟨_, _, _, _, _, _, Gm⟩ := S.hgrowth
  have hG : ContDiff ℝ ∞ (lineIter (multiDirs k) (scaledShell h n)) :=
    contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _
  have hm : ∀ j : ℕ, Measurable (A.indicator fun x => M.latticeApprox f
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) (j + 3)) := fun j =>
    (M.measurable_latticeApprox_translate_growth Gm S.hdeg S.hfT hG
      (fun v hv => lineIter_multiDirs_scaledShell_eq_zero_of_lt hh k n hv)
      (by omega : 3 ≤ j + 3)).indicator hA
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
    exact (tendsto_add_atTop_iff_nat 3).2
      (M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S k n (hAT x hx))
  · simp only [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds

end Model

end RegularityStructures

end
