/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesAuxWNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Profile.PolyPairing
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Heat.Schauder.Derivative

/-!
# The `τ`-terms of the series, near-pair `Γ`-bounds

For `τ = f(y) − Γ_{yx} f(x)`, `d = ‖y − x‖_𝔰`, `W = min (‖x‖_P, ‖y‖_P)` and `s = 2^n d`, the sums
`∑_i τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩` over `i` with `|k| < deg i + 2` (resp. `|k| ≥ deg i + 2`) are
bounded by `C K₀ C_f d^σ W^{η−γ} s^{-b}` for `s ≥ 1` (resp. `s^a` for `s ≤ 1`)
(`exists_abs_sum_tau_pairing_lt_le_win_near`, `exists_abs_sum_tau_pairing_ge_le_win_near`). In the
second case the polynomial `i` contribute `0` and the others have `|k| ≠ deg i + 2` by the
non-integrality hypothesis.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}
  {x y : ParabolicSpace}

/-- One `τ`-term: from `|B| ≤ C₀ K₀ (2^n)^p` and `|τ_i| ≤ C_f d^{γ−deg i} W^{η−γ}`,
`|τ_i B| ≤ C₀ K₀ C_f W^{η−γ} d^{γ−deg i−p} (2^n d)^p`. -/
theorem abs_tau_mul_le_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (P : SlabPair T x y) {i : ι}
    (hi : 𝒯.deg i < γ) {C₀ K₀ r : ℝ} (n : ℕ) {B : ℝ}
    (hp : |B| ≤ C₀ * K₀ * ((2 : ℝ) ^ n) ^ r) :
    |(f y - M.gammaMap y x (f x)) i * B| ≤ C₀ * K₀ * Cf *
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ) *
        (parabolicNorm (y - x) ^ (γ - 𝒯.deg i - r) *
          ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ r) := by
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hW := P.W_pos
  have h1 := M.abs_tau_le_win_near S P hi
  have hnn : 0 ≤ Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ) :=
    mul_nonneg (mul_nonneg S.hCf (Real.rpow_nonneg P.hd.le _)) (Real.rpow_nonneg hW.le _)
  rw [abs_mul]
  calc _ ≤ (Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
          (C₀ * K₀ * ((2 : ℝ) ^ n) ^ r) := mul_le_mul h1 hp (abs_nonneg _) hnn
    _ = C₀ * K₀ * Cf * min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
          (η - γ) * (parabolicNorm (y - x) ^ (γ - 𝒯.deg i) * ((2 : ℝ) ^ n) ^ r) := by ring
    _ = _ := by rw [rpow_mul_rpow_scale P.hd hu]

end Model

open Classical in
/-- The `τ`-terms with `|k| < deg i + 2`, for `s = 2^n d ≥ 1`: `≤ C K₀ C_f d^σ W^{η−γ} s^{-b}`. -/
theorem exists_abs_sum_tau_pairing_lt_le_win_near (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      1 ≤ (2 : ℝ) ^ n * parabolicNorm (y - x) →
      |∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
          (f y - M.gammaMap y x (f x)) i *
            parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
              (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
            ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ (-b) := by
  obtain ⟨C₀, hC₀, H⟩ := Model.exists_abs_pairing_shell_le_win_near hh k 𝒯 hdeg
  obtain ⟨b, hb, hbe⟩ := exists_pos_le_finset
    (Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ))
    (fun i => 𝒯.deg i + 2 - multiDeg k) (fun i hi => by
      have := (Finset.mem_filter.1 hi).2.1
      linarith)
  refine ⟨b, Fintype.card ι * C₀, hb, by positivity,
    fun M f T Cf CPi CGam S x y P n hs => ?_⟩
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := P.hd
  have hW := P.W_pos
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  set Cb : ℝ := C₀ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
      s ^ (-b) with hCb
  have hCb0 : 0 ≤ Cb := by
    have := S.hCf
    have : 0 ≤ s := by rw [hsdef]; positivity
    rw [hCb]
    positivity
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      |(f y - M.gammaMap y x (f x)) i *
        parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤ Cb := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    by_cases hτ : (f y - M.gammaMap y x (f x)) i = 0
    · rw [hτ, zero_mul, abs_zero]; exact hCb0
    · have hlt : 𝒯.deg i < γ := by
        by_contra hge
        exact hτ (M.tau_mem_lowerSubspace_win_near S x y i (not_lt.1 hge))
      have hp := H M y n i S.hPi S.hCPi S.hGam S.hgrowth P.hy.1.le (S.fst_le_one_of_mem_timeSlab P.hy) hlt
      have hbi : b ≤ 𝒯.deg i + 2 - multiDeg k :=
        hbe i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi', hlt⟩)
      have h1 := M.abs_tau_mul_le_win_near S P hlt n hp
      have e1 : γ - 𝒯.deg i - ((multiDeg k : ℝ) - 2 - 𝒯.deg i) = γ + 2 - multiDeg k := by ring
      have e2 : (multiDeg k : ℝ) - 2 - 𝒯.deg i = -(𝒯.deg i + 2 - multiDeg k) := by ring
      rw [e1, e2] at h1
      refine h1.trans ?_
      rw [hCb]
      have h2 := rpow_neg_le_of_one_le hs hbi
      have hX : 0 ≤ C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
          (singularWeight timeZeroDist y) ^ (η - γ) * parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) := by
        have := S.hCf
        positivity
      calc _ = (C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ) * parabolicNorm (y - x) ^
              (γ + 2 - multiDeg k)) * s ^ (-(𝒯.deg i + 2 - multiDeg k)) := by
            rw [hsdef]; ring
        _ ≤ (C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ) * parabolicNorm (y - x) ^
              (γ + 2 - multiDeg k)) * s ^ (-b) := mul_le_mul_of_nonneg_left h2 hX
        _ = _ := by ring
  calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2), |(f y -
        M.gammaMap y x (f x)) i * parabolicSemigroup.pairing
          (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2), Cb :=
        Finset.sum_le_sum hterm
    _ = (Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2)).card * Cb := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * Cb := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le _ _) hCb0
    _ = _ := by rw [hCb]; ring

open Classical in
/-- The `τ`-terms with `|k| ≥ deg i + 2`, for `s = 2^n d ≤ 1`: `≤ C K₀ C_f d^σ W^{η−γ} s^{a}`.
The polynomial components vanish, the others satisfy `|k| ≠ deg i + 2` by `hni`. -/
theorem exists_abs_sum_tau_pairing_ge_le_win_near (hh : ShellProfile h N) (hN : N' ≤ N)
    (k : Fin 4 →₀ ℕ) (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (P : PolynomialSector 𝒯 N')
    {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hni : ∀ i, i ∉ Set.range P.emb → (Pi.single i 1 : ι → ℝ) ∈ V → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P →
      (∀ z, f z ∈ V) → ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      (2 : ℝ) ^ n * parabolicNorm (y - x) ≤ 1 →
      |∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
          (f y - M.gammaMap y x (f x)) i *
            parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
              (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
            ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ a := by
  obtain ⟨C₀, hC₀, H⟩ := Model.exists_abs_pairing_shell_le_win_near hh k 𝒯 hdeg
  obtain ⟨a, ha, hae⟩ := exists_pos_le_finset
    (Finset.univ.filter (fun i => i ∉ Set.range P.emb ∧ (Pi.single i 1 : ι → ℝ) ∈ V ∧
      𝒯.deg i < γ ∧ ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2))
    (fun i => (multiDeg k : ℝ) - 2 - 𝒯.deg i) (fun i hi => by
      obtain ⟨h1, h2, h3, h4⟩ := (Finset.mem_filter.1 hi).2
      have := hni i h1 h2 h3
      rcases lt_or_gt_of_ne this with h | h
      · exact absurd h h4
      · linarith)
  refine ⟨a, Fintype.card ι * C₀, ha, by positivity,
    fun M f T Cf CPi CGam S hpoly hfV x y Pr n hs => ?_⟩
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := Pr.hd
  have hW := Pr.W_pos
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  set Cb : ℝ := C₀ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ)) *
      s ^ a with hCb
  have hCb0 : 0 ≤ Cb := by
    have := S.hCf
    rw [hCb]
    positivity
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
      |(f y - M.gammaMap y x (f x)) i *
        parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤ Cb := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    by_cases hτ : (f y - M.gammaMap y x (f x)) i = 0
    · rw [hτ, zero_mul, abs_zero]; exact hCb0
    · obtain ⟨hVi, hlt⟩ := M.tau_support_slab_win_near S hV hVb hfV x y hτ
      by_cases hem : i ∈ Set.range P.emb
      · have h0 := Model.derivShellPairing_regPi_emb_eq_zeroP hpoly hh hN y hem k n
        unfold derivShellPairing at h0
        rw [h0, mul_zero, abs_zero]; exact hCb0
      · have hae' : a ≤ (multiDeg k : ℝ) - 2 - 𝒯.deg i :=
          hae i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hem, hVi, hlt, hi'⟩)
        have hp := H M y n i S.hPi S.hCPi S.hGam S.hgrowth Pr.hy.1.le (S.fst_le_one_of_mem_timeSlab Pr.hy) hlt
        have h1 := M.abs_tau_mul_le_win_near S Pr hlt n hp
        have e1 : γ - 𝒯.deg i - ((multiDeg k : ℝ) - 2 - 𝒯.deg i) = γ + 2 - multiDeg k := by ring
        rw [e1] at h1
        refine h1.trans ?_
        rw [hCb]
        have h2 := rpow_le_of_le_one hs0 hs hae'
        have hX : 0 ≤ C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
            (singularWeight timeZeroDist y) ^ (η - γ) *
              parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) := by
          have := S.hCf
          positivity
        calc _ = (C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
              (singularWeight timeZeroDist y) ^ (η - γ) * parabolicNorm (y - x) ^
                (γ + 2 - multiDeg k)) * s ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg i) := by
              rw [hsdef]; ring
          _ ≤ (C₀ * (max 1 CGam * CPi) * Cf * min (singularWeight timeZeroDist x)
              (singularWeight timeZeroDist y) ^ (η - γ) * parabolicNorm (y - x) ^
                (γ + 2 - multiDeg k)) * s ^ a := mul_le_mul_of_nonneg_left h2 hX
          _ = _ := by ring
  calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2), |(f y -
        M.gammaMap y x (f x)) i * parabolicSemigroup.pairing
          (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2), Cb :=
        Finset.sum_le_sum hterm
    _ = (Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2)).card * Cb := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * Cb := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le _ _) hCb0
    _ = _ := by rw [hCb]; ring

end RegularityStructures

end
