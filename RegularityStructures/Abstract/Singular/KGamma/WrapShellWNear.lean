/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.WindowAt.SlabNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellG
public import RegularityStructures.Abstract.Singular.Local.Const
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Shell pairing bounds, near-pair `Γ`-bounds

Bounds on the shell pairings: the small-scale bound on
`⟨R f, D^k K_n(x − ·)⟩ − ⟨Π_x f(x), D^k K_n(x − ·)⟩` for `64 · 2^{-n} ≤ ‖x‖_P`, the layer bound and
the time-Taylor bound (`x₀ ≤ 4^{-n}`) on `⟨R f, D^k K_n(x − ·)⟩`, and the bound
`C K₀ 2^{(|k| − 2 − deg i) n}` on `⟨Π_x e_i, D^k K_n(x − ·)⟩`, for models whose `Γ`-bounds hold only
for near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place
of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

namespace Model

variable {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
  (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)

include hh hc in
/-- Small scales, window models:
`|⟨R f, D^k K_n(x − ·)⟩ − ⟨Π_x f(x), D^k K_n(x − ·)⟩| ≤ C K₀ C_f 2^{(|k| − 2 − γ) n} ‖x‖_P^{η−γ}`
for `64 · 2^{-n} ≤ ‖x‖_P`. -/
theorem exists_abs_singShellPairing_le_win_near (𝒯 : RegularityStructure ι) {γ : ℝ}
    (η : ℝ) (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ} {x : ParabolicSpace}
      (n : ℕ), M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 →
      (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f → x ∈ timeSlab T →
      64 * ((2 : ℝ) ^ n)⁻¹ ≤ singularWeight timeZeroDist x →
      |M.singShellPairing h f x k n| ≤
        C * (max 1 CGam * CPi) * Cf * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - γ) *
          singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_sub_pairing_le_of_scaled_win_near 𝒯 η hγ hdeg
  obtain ⟨Cs, hCs, hS⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  refine ⟨Cl * Cs, by positivity,
    fun M {CPi CGam Cf f T x} n hPi hCPi hGam hgrowth hT1 hfT hf hx hxw => ?_⟩
  have hvan : ∀ w : ParabolicSpace, T < w.1 →
      lineIter (multiDirs k) (scaledShell h n) (x - w) = 0 := fun w hw =>
    lineIter_multiDirs_scaledShell_sub_eq_zero hh.contDiff hc k n (hx.2.trans hw.le)
  obtain ⟨_, hb⟩ := hCl M hPi hCPi hGam hgrowth hT1 hfT hf (hS n x) hx hxw hvan
  have key := shell_scale_eq (u := (2 : ℝ) ^ n) (by positivity) Cs (multiDeg k) γ
  unfold singShellPairing
  refine hb.trans (le_of_eq ?_)
  rw [key]
  ring

include hh hc in
/-- The layer bound for the shell derivatives, window models: for every `x` in the slab and
every `n`, `|⟨R f, D^k K_n(x − ·)⟩| ≤ C K₀ C_f 2^{(|k| − 2 − α ∧ η) n}`. -/
theorem exists_abs_latticeRecon_shell_le_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ,
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf *
          ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - min α η) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_scaled_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨Cs, hCs, hS⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  refine ⟨Cl * Cs, by positivity, fun M f T Cf CPi CGam S x hx n => ?_⟩
  have hvan : ∀ w : ParabolicSpace, T < w.1 →
      lineIter (multiDirs k) (scaledShell h n) (x - w) = 0 := fun w hw =>
    lineIter_multiDirs_scaledShell_sub_eq_zero hh.contDiff hc k n (hx.2.trans hw.le)
  obtain ⟨_, hb⟩ := hCl M f T Cf CPi CGam S (hS n x) hvan
  have key := shell_scale_eq (u := (2 : ℝ) ^ n) (by positivity) Cs (multiDeg k) (min α η)
  refine hb.trans (le_of_eq ?_)
  rw [key]
  ring

include hh in
/-- `⟨Π_x e_i, D^k K_n(x − ·)⟩` is bounded by `C K₀ 2^{(|k| − 2 − deg i) n}` for `x` with
`0 ≤ x₀ ≤ 1` (window models). -/
theorem exists_abs_pairing_shell_le_win_near (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      (x : ParabolicSpace) (n : ℕ) (i : ι),
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      0 ≤ x.1 → x.1 ≤ 1 → 𝒯.deg i < γ →
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
          (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i) := by
  obtain ⟨Cs, hCs, hS⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  refine ⟨max 0 (r4ModelConst 𝒯 γ * Cs), le_max_left _ _,
    fun M {CPi CGam} x n i hPi hCPi hGam hgrowth hx0 hx1 hi => ?_⟩
  have hfin : (Finset.univ.filter (fun j => 𝒯.deg j < γ)).sum
      (fun j => |(Pi.single i (1 : ℝ) : ι → ℝ) j| * ((2 : ℝ) ^ n)⁻¹ ^ 𝒯.deg j) =
      ((2 : ℝ) ^ n)⁻¹ ^ 𝒯.deg i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hni
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩) hni
  have hτ : (Pi.single i (1 : ℝ) : ι → ℝ) ∈ lowerSubspace 𝒯.deg γ := by
    intro j hj
    have hne : j ≠ i := fun h => absurd hj (by rw [h]; exact not_le.2 hi)
    exact Pi.single_eq_of_ne hne _
  have := M.abs_pairing_regPi_le_of_scaled_slabAt_near hPi hCPi hGam
    (M.hasQualitativeGrowthAt_of_exists hgrowth x) hdeg hx0 hx1 hτ (hS n x)
  rw [hfin] at this
  have key := shell_scale_eq (u := (2 : ℝ) ^ n) (by positivity) Cs (multiDeg k) (𝒯.deg i)
  have hK : 0 ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) :=
    mul_nonneg (r4ModelConst_nonneg 𝒯 hdeg)
      (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi)
  have hX : 0 ≤ (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi) (by positivity)
  calc _ ≤ _ := this
    _ = (r4ModelConst 𝒯 γ * Cs) * ((max 1 CGam * CPi) *
        ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i)) := by
        linear_combination (r4ModelConst 𝒯 γ * (max 1 CGam * CPi)) * key
    _ ≤ max 0 (r4ModelConst 𝒯 γ * Cs) * ((max 1 CGam * CPi) *
        ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hX
    _ = _ := by ring

include hh hc in
/-- Time-Taylor bound (window models): for `x` in the slab, `1 ≤ n` and `x₀ ≤ 4^{-n}`,
`|⟨R f, D^k K_n(x − ·)⟩| ≤ C K₀ C_f (x₀ 4^n)^m 2^{(|k| − 2 − α ∧ η) n}`. -/
theorem exists_abs_latticeRecon_shell_le_timeTaylor_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ, 1 ≤ n → x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 →
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * (x.1 * 4 ^ n) ^ m *
          ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - min α η) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_scaled_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨Ct, hCt, hT⟩ := exists_isScaledTest_shellTimeTaylorRem_const hh k m
  refine ⟨Cl * Ct * (2 ^ 5 * 2 ^ (min α η)), by positivity,
    fun M f T Cf CPi CGam S x hx n hn hxn => ?_⟩
  have hx0 : 0 < x.1 := hx.1
  have hpos : 0 < (x.1 * 4 ^ n) ^ m := by positivity
  have hrem := hT n hn x hx0.le hxn hpos
  have hf0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0 := fun z hz =>
    S.hf0 z fun hzs => absurd hz (not_le.2 hzs.1)
  have hGT : ∀ w : ParabolicSpace, T < w.1 →
      lineIter (multiDirs k) (scaledShell h n) (x - w) = 0 := fun w hw =>
    lineIter_multiDirs_scaledShell_sub_eq_zero hh.contDiff hc k n (hx.2.trans hw.le)
  have hremT : ∀ w : ParabolicSpace, T < w.1 → shellTimeTaylorRem h k m n x w = 0 := fun w hw => by
    unfold shellTimeTaylorRem
    rw [hGT w hw, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun j _ => by
      rw [lineIter_multiDirs_scaledShell_projection_eq_zero hh.contDiff hc _ n x.2
        (hx0.le.trans (hx.2.trans hw.le)), mul_zero]
  obtain ⟨ht1, hb⟩ := hCl M f T Cf CPi CGam S hrem hremT
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hR := M.latticeRecon_shell_eq_rem_growth hh hc k G S.hdeg S.hfT hf0 m n hrem.supp
    ht1
  rw [hR]
  refine hb.trans (le_of_eq ?_)
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key := shell_scale_eq hu (Ct * (x.1 * 4 ^ n) ^ m) (multiDeg k) (min α η)
  have h5 : (2 * ((2 : ℝ) ^ n)⁻¹) ^ 5 = 2 ^ 5 * (((2 : ℝ) ^ n)⁻¹) ^ 5 := mul_pow _ _ _
  have hmm : (2 * ((2 : ℝ) ^ n)⁻¹) ^ (min α η) =
      2 ^ (min α η) * (((2 : ℝ) ^ n)⁻¹) ^ (min α η) :=
    Real.mul_rpow (by norm_num) (by positivity)
  rw [h5, hmm]
  linear_combination (Cl * (max 1 CGam * CPi) * Cf * (2 ^ 5 * 2 ^ (min α η))) * key

end Model

end RegularityStructures

end
