/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesTauWNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.Bracket
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# The series for small scales `2^{-n} < d`, near-pair `Γ`-bounds

For `s = 2^n d > 1` the term `polyUS n` is estimated directly from its definition: the `τ`-terms
with `|k| < deg i + 2`, the shell pairing at `y` (`exists_abs_singShellPairing_le_W_win_near`), and
the Taylor terms `(y−x)^l/l! ⟨Rf − Π_x f(x), D^{k+l} K_n(x−·)⟩`
(`exists_abs_taylor_shell_sum_le_win_near`), all by the local bound. Result:
`|polyUS n| ≤ C K₀ C_f d^σ W^{η−γ} s^{-b}` (`exists_abs_polyUS_le_of_one_lt_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

/-- The local bound for the singular shell pairing with the weight `W` of a close pair. -/
theorem exists_abs_singShellPairing_le_W_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {z : ParabolicSpace} {W : ℝ}, z ∈ timeSlab T → 0 < W → W ≤ singularWeight timeZeroDist z →
      singularWeight timeZeroDist z ≤ 2 * W → ∀ n : ℕ, 64 * ((2 : ℝ) ^ n)⁻¹ ≤ W →
      |M.singShellPairing h f z k n| ≤
        C * (max 1 CGam * CPi) * Cf * (W ^ (η - γ) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - γ)) := by
  obtain ⟨Cl, hCl0, hCl⟩ := Model.exists_abs_singShellPairing_le_win_near hh hc k 𝒯 η hγ hdeg
  refine ⟨Cl * 2 ^ |η - γ|, by positivity,
    fun M f T Cf CPi CGam S z W hz hW hw1 hw2 n hn => ?_⟩
  have h1 := hCl M n S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf hz (hn.trans hw1)
  have h2 := rpow_weight_le hW hw1 hw2 (η - γ)
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hX : 0 ≤ Cl * (max 1 CGam * CPi) * Cf * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - γ) := by
    have := S.hCf
    positivity
  refine h1.trans ?_
  calc _ = (Cl * (max 1 CGam * CPi) * Cf * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - γ)) *
        singularWeight timeZeroDist z ^ (η - γ) := by ring
    _ ≤ (Cl * (max 1 CGam * CPi) * Cf * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - γ)) *
        (2 ^ |η - γ| * W ^ (η - γ)) := mul_le_mul_of_nonneg_left h2 hX
    _ = _ := by ring

/-- The Taylor terms at `x` for `s = 2^n d ≥ 1`:
`|∑_{|l| < σ} c_l(y−x) ⟨R f − Π_x f(x), D^{k+l}K_n(x−·)⟩| ≤ C K₀ C_f d^σ W^{η−γ} s^{-b}`. -/
theorem exists_abs_taylor_shell_sum_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      1 ≤ (2 : ℝ) ^ n * parabolicNorm (y - x) →
      |∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
          M.singShellPairing h f x (k + l) n| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
            ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ (-b) := by
  classical
  have hex : ∀ l : Fin 4 →₀ ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup)
      (f : ParabolicSpace → ι → ℝ) (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {z : ParabolicSpace} {W : ℝ}, z ∈ timeSlab T → 0 < W →
      W ≤ singularWeight timeZeroDist z → singularWeight timeZeroDist z ≤ 2 * W →
      ∀ n : ℕ, 64 * ((2 : ℝ) ^ n)⁻¹ ≤ W →
      |M.singShellPairing h f z (k + l) n| ≤
        C * (max 1 CGam * CPi) * Cf *
          (W ^ (η - γ) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - γ)) :=
    fun l => exists_abs_singShellPairing_le_W_win_near hh hc (k + l) 𝒯 η α hγ hdeg
  choose Cl hCl0 hCl using hex
  obtain ⟨b, hb, hbe⟩ := exists_pos_le_finset (taylorIdx (γ + 2 - multiDeg k))
    (fun l => γ + 2 - multiDeg k - multiDeg l) (fun l hl => by
      have := (mem_taylorIdx_iff l).1 hl
      linarith)
  refine ⟨b, ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), Cl l, hb,
    Finset.sum_nonneg fun l _ => hCl0 l, fun M f T Cf CPi CGam S x y Pr n hs => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have h64 : 64 * ((2 : ℝ) ^ n)⁻¹ ≤
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) := by
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ parabolicNorm (y - x) := by
      rw [inv_le_iff_one_le_mul₀ hu]; rw [hsdef] at hs; linarith
    have := Pr.hW
    linarith
  set Y : ℝ := (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
      s ^ (-b) with hY
  have hY0 : 0 ≤ Y := by
    have := S.hCf
    rw [hY]; positivity
  have hterm : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k),
      |coeffT (parabolicCoords (y - x)) l * M.singShellPairing h f x (k + l) n| ≤ Cl l * Y := by
    intro l hl
    have hlt := (mem_taylorIdx_iff l).1 hl
    have hbl : b ≤ γ + 2 - multiDeg k - multiDeg l := hbe l hl
    have hsing := hCl l M f T Cf CPi CGam S Pr.hx hW Pr.W_le_x Pr.x_le_two_W n h64
    have hcoef : |coeffT (parabolicCoords (y - x)) l| ≤ parabolicNorm (y - x) ^ multiDeg l :=
      abs_coeffT_le (fun j => abs_parabolicCoords_le j) l
    rw [abs_mul]
    have hmd : ((multiDeg (k + l) : ℕ) : ℝ) = multiDeg k + multiDeg l := by
      have hadd : multiDeg (k + l) = multiDeg k + multiDeg l := map_add _ _ _
      rw [hadd]; push_cast; ring
    rw [hmd] at hsing
    have hp : (multiDeg k : ℝ) + multiDeg l - 2 - γ = -(γ + 2 - multiDeg k - multiDeg l) := by ring
    rw [hp] at hsing
    have hdl : parabolicNorm (y - x) ^ multiDeg l = parabolicNorm (y - x) ^ ((multiDeg l : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    have hsc := rpow_mul_rpow_scale hd hu ((multiDeg l : ℕ) : ℝ)
      (-(γ + 2 - multiDeg k - multiDeg l))
    have e1 : ((multiDeg l : ℕ) : ℝ) - -(γ + 2 - multiDeg k - multiDeg l) = γ + 2 - multiDeg k := by
      ring
    rw [e1] at hsc
    have hneg := rpow_neg_le_of_one_le hs hbl
    have hA0 : 0 ≤ Cl l * (max 1 CGam * CPi) * Cf * (min (singularWeight timeZeroDist x)
        (singularWeight timeZeroDist y) ^ (η - γ)) := by
      have := S.hCf; have := hCl0 l
      positivity
    calc |coeffT (parabolicCoords (y - x)) l| * |M.singShellPairing h f x (k + l) n|
        ≤ parabolicNorm (y - x) ^ multiDeg l * (Cl l * (max 1 CGam * CPi) * Cf *
          (min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ) *
            ((2 : ℝ) ^ n) ^ (-(γ + 2 - multiDeg k - multiDeg l)))) :=
          mul_le_mul hcoef hsing (abs_nonneg _) (pow_nonneg (parabolicNorm_nonneg _) _)
      _ = (Cl l * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ)) *
            (parabolicNorm (y - x) ^ ((multiDeg l : ℕ) : ℝ) *
              ((2 : ℝ) ^ n) ^ (-(γ + 2 - multiDeg k - multiDeg l))) := by rw [hdl]; ring
      _ = (Cl l * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ)) *
            (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
              s ^ (-(γ + 2 - multiDeg k - multiDeg l))) := by rw [hsc]
      _ ≤ (Cl l * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ)) *
            (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) * s ^ (-b)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hneg
            (Real.rpow_nonneg hd.le _)) hA0
      _ = _ := by rw [hY]; ring
  calc _ ≤ ∑ l ∈ taylorIdx (γ + 2 - multiDeg k),
        |coeffT (parabolicCoords (y - x)) l * M.singShellPairing h f x (k + l) n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), Cl l * Y := Finset.sum_le_sum hterm
    _ = (∑ l ∈ taylorIdx (γ + 2 - multiDeg k), Cl l) * Y := by rw [Finset.sum_mul]
    _ = _ := by rw [hY]; ring

/-- **Small scales** `2^{-n} < d`: `|polyUS n| ≤ C K₀ C_f d^σ W^{η−γ} s^{-b}`, `s = 2^n d > 1`. -/
theorem exists_abs_polyUS_le_of_one_lt_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hkγ : (multiDeg k : ℝ) < γ + 2) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      1 < (2 : ℝ) ^ n * parabolicNorm (y - x) →
      |polyUS M h γ f x y k n| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
            ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ (-b) := by
  obtain ⟨b₁, C₁, hb₁, hC₁, H₁⟩ := exists_abs_sum_tau_pairing_lt_le_win_near hh k 𝒯 η α hdeg
  obtain ⟨b₂, C₂, hb₂, hC₂, H₂⟩ := exists_abs_taylor_shell_sum_le_win_near hh hc k 𝒯 η α hγ hdeg
  obtain ⟨Cy, hCy, Hy⟩ := exists_abs_singShellPairing_le_W_win_near hh hc k 𝒯 η α hγ hdeg
  have hσ : 0 < γ + 2 - (multiDeg k : ℝ) := by linarith
  set σ : ℝ := γ + 2 - multiDeg k with hσdef
  refine ⟨min b₁ (min b₂ σ), C₁ + Cy + C₂, lt_min hb₁ (lt_min hb₂ hσ), by positivity,
    fun M f T Cf CPi CGam S x y Pr n hs => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  have hs1 : 1 ≤ s := hs.le
  set Y : ℝ := (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) with hY
  have hY0 : 0 ≤ Y := by
    have := S.hCf
    rw [hY]; positivity
  have hb : ∀ b', min b₁ (min b₂ σ) ≤ b' → s ^ (-b') ≤ s ^ (-(min b₁ (min b₂ σ))) :=
    fun b' hb' => rpow_neg_le_of_one_le hs1 hb'
  have hA := H₁ M f T Cf CPi CGam S Pr n hs1
  have hE := H₂ M f T Cf CPi CGam S Pr n hs1
  -- the singular shell pairing at `y`
  have h64 : 64 * ((2 : ℝ) ^ n)⁻¹ ≤
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) := by
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ parabolicNorm (y - x) := by
      rw [inv_le_iff_one_le_mul₀ hu]; rw [hsdef] at hs1; linarith
    have := Pr.hW
    linarith
  have hB := Hy M f T Cf CPi CGam S Pr.hy hW Pr.W_le_y Pr.y_le_two_W n h64
  have hscale := rpow_mul_rpow_scale hd hu 0 (-σ)
  rw [Real.rpow_zero, one_mul, zero_sub, neg_neg] at hscale
  have hp : (multiDeg k : ℝ) - 2 - γ = -σ := by rw [hσdef]; ring
  rw [hp] at hB
  have hB' : |M.singShellPairing h f y k n| ≤ Cy * Y * s ^ (-σ) := by
    refine hB.trans (le_of_eq ?_)
    rw [hscale, hY]; ring
  have hσb : s ^ (-σ) ≤ s ^ (-(min b₁ (min b₂ σ))) :=
    hb σ ((min_le_right _ _).trans (min_le_right _ _))
  have hA' : |∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      (f y - M.gammaMap y x (f x)) i * parabolicSemigroup.pairing
        (fun t z => M.regPi y (Pi.single i 1) t z)
        (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤
      C₁ * Y * s ^ (-(min b₁ (min b₂ σ))) := by
    refine hA.trans ?_
    have := hb b₁ (min_le_left _ _)
    rw [hY] at *
    have hX : 0 ≤ C₁ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) := by
      have := S.hCf; positivity
    calc _ ≤ C₁ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
          s ^ (-(min b₁ (min b₂ σ))) := mul_le_mul_of_nonneg_left this hX
      _ = _ := by ring
  have hE' : |∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
      M.singShellPairing h f x (k + l) n| ≤ C₂ * Y * s ^ (-(min b₁ (min b₂ σ))) := by
    refine hE.trans ?_
    have := hb b₂ ((min_le_right _ _).trans (min_le_left _ _))
    have hX : 0 ≤ C₂ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) := by
      have := S.hCf; positivity
    calc _ ≤ C₂ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
          s ^ (-(min b₁ (min b₂ σ))) := mul_le_mul_of_nonneg_left this hX
      _ = _ := by rw [hY]; ring
  have hB'' : |M.singShellPairing h f y k n| ≤ Cy * Y * s ^ (-(min b₁ (min b₂ σ))) :=
    hB'.trans (mul_le_mul_of_nonneg_left hσb (mul_nonneg hCy hY0))
  unfold polyUS
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) hE').trans ?_
  have := add_le_add_left (add_le_add hA' hB'') (C₂ * Y * s ^ (-(min b₁ (min b₂ σ))))
  refine this.trans (le_of_eq ?_)
  rw [hY]; ring

end RegularityStructures

end
