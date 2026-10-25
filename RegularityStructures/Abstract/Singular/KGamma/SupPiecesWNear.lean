/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Radius2WNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Weighted shell bounds for the sup estimate of `𝒦_γ f`, near-pair `Γ`-bounds

The layer bound, the time-Taylor bound (for `t < 1`), the bound on
`f(x)_i ⟨Π_x e_i, D^k K_n(x − ·)⟩` (for `α ≤ deg i < γ`) and the local bound (for `t ≥ 64`) on the
shell pairings, written in terms of the weight `w` of `x` and `t = 2^n w`, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

namespace RegularityStructures.KGammaSup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
  (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)

include hh hc in
/-- Layer bound in terms of `w` and `t`. -/
theorem exists_abs_latticeRecon_shell_le_weight_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ,
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) *
          ((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^ ((multiDeg k : ℝ) - 2 - min α η) := by
  obtain ⟨C, hC0, hC⟩ := Model.exists_abs_latticeRecon_shell_le_win_near hh hc k 𝒯 γ η α hdeg hγ hαγ hαη
  refine ⟨C, hC0, fun M f T Cf CPi CGam S x hx n => ?_⟩
  refine (hC M f T Cf CPi CGam S hx n).trans ?_
  have hK : 0 ≤ C * (max 1 CGam * CPi) * Cf :=
    mul_nonneg (mul_nonneg hC0 S.hK0) S.hCf
  have := mul_rpow_mul_rpow_le (u := (2 : ℝ) ^ n) (w := singularWeight timeZeroDist x)
    (by positivity) (weight_pos hx) (singularWeight_le_one _ _) hK
    (e := (multiDeg k : ℝ) - 2 - min α η) (s := 0) (s' := min α η + 2 - multiDeg k) (by linarith)
  rw [Real.rpow_zero, mul_one] at this
  refine this.trans (le_of_eq ?_)
  ring

include hh hc in
/-- Time-Taylor bound in terms of `w` and `t`, for `t < 1`. -/
theorem exists_abs_latticeRecon_shell_le_weight_small_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ, (2 : ℝ) ^ n * singularWeight timeZeroDist x < 1 →
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) *
          ((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^
            (2 * (m : ℝ) + ((multiDeg k : ℝ) - 2 - min α η)) := by
  obtain ⟨C, hC0, hC⟩ := Model.exists_abs_latticeRecon_shell_le_timeTaylor_all_win_near hh hc k 𝒯 γ η α
    hdeg hγ hαγ hαη m
  refine ⟨C, hC0, fun M f T Cf CPi CGam S x hx n ht => ?_⟩
  have hxn := le_inv_sq_of_scale_lt_one hx n ht
  refine (hC M f T Cf CPi CGam S hx n hxn).trans ?_
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hw := weight_pos hx
  have hw1 : singularWeight timeZeroDist x < 1 := by
    have hu1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hx1 : x.1 = singularWeight timeZeroDist x ^ 2 := (weight_sq_eq hx hw1).symm
  have hK : 0 ≤ C * (max 1 CGam * CPi) * Cf :=
    mul_nonneg (mul_nonneg hC0 S.hK0) S.hCf
  set w := singularWeight timeZeroDist x with hwdef
  set e : ℝ := (multiDeg k : ℝ) - 2 - min α η with he
  have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : (x.1 * 4 ^ n) ^ m = ((2 : ℝ) ^ n * w) ^ (2 * (m : ℝ)) := by
    have : x.1 * 4 ^ n = ((2 : ℝ) ^ n * w) ^ 2 := by rw [hx1, h4]; ring
    rw [this, ← pow_mul, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have e2 := rpow_eq_rpow_mul_rpow_neg hu hw e
  have e3 : ((2 : ℝ) ^ n * w) ^ (2 * (m : ℝ)) * ((2 : ℝ) ^ n * w) ^ e =
      ((2 : ℝ) ^ n * w) ^ (2 * (m : ℝ) + e) :=
    (Real.rpow_add (by positivity) _ _).symm
  have e4 : w ^ (-e) = w ^ (min α η + 2 - multiDeg k) := by
    congr 1; rw [he]; ring
  refine le_of_eq ?_
  calc C * (max 1 CGam * CPi) * Cf * (x.1 * 4 ^ n) ^ m * ((2 : ℝ) ^ n) ^ e
      = C * (max 1 CGam * CPi) * Cf * (((2 : ℝ) ^ n * w) ^ (2 * (m : ℝ)) *
          (((2 : ℝ) ^ n * w) ^ e * w ^ (-e))) := by rw [e1, e2]; ring
    _ = C * (max 1 CGam * CPi) * Cf * w ^ (min α η + 2 - multiDeg k) *
          ((2 : ℝ) ^ n * w) ^ (2 * (m : ℝ) + e) := by rw [← e3, e4]; ring

include hh in
/-- `|f(x)_i ⟨Π_x e_i, D^k K_n(x − ·)⟩|` in terms of `w` and `t`, for `α ≤ deg i < γ`. -/
theorem exists_abs_fx_mul_pairing_shell_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ (n : ℕ) (i : ι), α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      |f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
          (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) *
          ((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i) := by
  obtain ⟨Cb, hCb0, hCb⟩ := Model.exists_abs_pairing_shell_le_win_near hh k 𝒯 hdeg
  refine ⟨Cb, hCb0, fun M f T Cf CPi CGam S x hx n i hαi hi => ?_⟩
  have hw := weight_pos hx
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hf1 := S.hf.1 x hx (timeZeroDist_pos_of_mem_timeSlab hx) i hi
  have hb1 := hCb M x n i S.hPi S.hCPi S.hGam S.hgrowth hx.1.le (S.fst_le_one_of_mem_timeSlab hx) hi
  have hK : 0 ≤ Cb * (max 1 CGam * CPi) * Cf :=
    mul_nonneg (mul_nonneg hCb0 S.hK0) S.hCf
  rw [abs_mul]
  have hCf := S.hCf
  have hprod : |f x i| * |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
      (Cf * singularWeight timeZeroDist x ^ min (η - 𝒯.deg i) 0) *
        (Cb * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i)) :=
    mul_le_mul hf1 hb1 (abs_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg hw.le _))
  refine hprod.trans ?_
  have hmain := mul_rpow_mul_rpow_le (u := (2 : ℝ) ^ n) (w := singularWeight timeZeroDist x)
    hu hw (singularWeight_le_one _ _) hK
    (e := (multiDeg k : ℝ) - 2 - 𝒯.deg i) (s := min (η - 𝒯.deg i) 0)
    (s' := min α η + 2 - multiDeg k) (by
      have : min α η ≤ min (η - 𝒯.deg i) 0 + 𝒯.deg i := by
        rcases le_total (η - 𝒯.deg i) 0 with h0 | h0
        · rw [min_eq_left h0]; linarith [min_le_right α η]
        · rw [min_eq_right h0]; linarith [min_le_left α η]
      linarith)
  refine (le_of_eq ?_).trans (hmain.trans (le_of_eq ?_)) <;> ring

include hh hc in
/-- The local bound in terms of `w` and `t`, for `t ≥ 64`. -/
theorem exists_abs_singShellPairing_le_weight_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ, 64 ≤ (2 : ℝ) ^ n * singularWeight timeZeroDist x →
      |M.singShellPairing h f x k n| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) *
          ((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^ ((multiDeg k : ℝ) - 2 - γ) := by
  obtain ⟨C, hC0, hC⟩ := Model.exists_abs_singShellPairing_le_win_near hh hc k 𝒯 η hγ hdeg
  refine ⟨C, hC0, fun M f T Cf CPi CGam S x hx n hn => ?_⟩
  have hw := weight_pos hx
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h64 : 64 * ((2 : ℝ) ^ n)⁻¹ ≤ singularWeight timeZeroDist x := by
    rw [← div_eq_mul_inv, div_le_iff₀ hu]; linarith
  refine (hC M n S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf hx h64).trans ?_
  have hK : 0 ≤ C * (max 1 CGam * CPi) * Cf :=
    mul_nonneg (mul_nonneg hC0 S.hK0) S.hCf
  have hmain := mul_rpow_mul_rpow_le (u := (2 : ℝ) ^ n) (w := singularWeight timeZeroDist x)
    hu hw (singularWeight_le_one _ _) hK
    (e := (multiDeg k : ℝ) - 2 - γ) (s := η - γ) (s' := min α η + 2 - multiDeg k)
    (by linarith [min_le_right α η])
  refine (le_of_eq ?_).trans (hmain.trans (le_of_eq ?_)) <;> ring

end RegularityStructures.KGammaSup

end
