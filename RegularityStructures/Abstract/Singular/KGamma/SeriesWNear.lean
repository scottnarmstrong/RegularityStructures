/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesRegionWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesSmallWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.KGamma.Bracket
public import RegularityStructures.Abstract.Singular.KGamma.Geom
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.KGamma.SeriesBig

/-!
# The polynomial series of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`, near-pair `Γ`-bounds

The two-scale bound `|polyUS n| ≤ C K₀ C_f d^σ W^{α∧η−γ} min(s^a, s^{-b})`, `s = 2^n d`, and [Hai14,
Prop. 6.16]: for `x, y` in the time slab with `0 < d = ‖y − x‖_𝔰`, `64 d ≤ W = min(‖x‖_P, ‖y‖_P)`
and `|k|_𝔰 < γ + 2`, `|∑_n polyUS n| ≤ C K₀ C_f d^{γ+2−|k|} W^{α∧η−γ}`, for models whose `Γ`-bounds
hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

/-- The two-scale bound for a single term of the series: `|polyUS n| ≤ C K₀ C_f d^σ W^{α∧η−γ}
min (s^a, s^{-b})`, `s = 2^n d`. -/
theorem exists_abs_polyUS_le_min_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (hN : N' ≤ N) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hαγ : α ≤ γ) (hαη : -2 < min α η)
    (hkγ : (multiDeg k : ℝ) < γ + 2)
    (hnat : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (P : PolynomialSector 𝒯 N') {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hni : ∀ i, i ∉ Set.range P.emb → (Pi.single i 1 : ι → ℝ) ∈ V → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ a b C : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup)
      (f : ParabolicSpace → ι → ℝ) (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P → (∀ z, f z ∈ V) →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      |polyUS M h γ f x y k n| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
            (min α η - γ)) *
          min (((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ a)
            (((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ (-b)) := by
  obtain ⟨b, Cs, hb, hCs, Hs⟩ := exists_abs_polyUS_le_of_one_lt_win_near hh hc k 𝒯 η α hγ hdeg hkγ
  obtain ⟨a, Cl, ha, hCl, Hl⟩ := exists_abs_polyUS_le_of_le_one_win_near hh hc hN k 𝒯 η α hγ hdeg hαγ hαη
    hkγ hnat P hV hVb hni
  refine ⟨a, b, max Cs Cl, ha, hb, hCs.trans (le_max_left _ _),
    fun M f T Cf CPi CGam S hpoly hfV x y Pr n => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hWdef
  set Z : ℝ := (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
    W ^ (min α η - γ)) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  rcases le_or_gt s 1 with hs1 | hs1
  · have := Hl M f T Cf CPi CGam S hpoly hfV Pr n hs1
    have hmin : min (s ^ a) (s ^ (-b)) = s ^ a := by
      refine min_eq_left ?_
      calc s ^ a ≤ 1 := Real.rpow_le_one hs0.le hs1 ha.le
        _ ≤ s ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith)
    rw [hmin]
    have e : Cl * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
        W ^ (min α η - γ)) * s ^ a = Cl * Z * s ^ a := by rw [hZ]; ring
    refine this.trans ?_
    rw [e]
    calc Cl * Z * s ^ a ≤ max Cs Cl * Z * s ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hZ0)
            (Real.rpow_nonneg hs0.le _)
      _ = _ := by rw [hZ]; ring
  · have := Hs M f T Cf CPi CGam S Pr n hs1
    have hmin : min (s ^ a) (s ^ (-b)) = s ^ (-b) := by
      refine min_eq_right ?_
      calc s ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1.le (by linarith)
        _ ≤ s ^ a := Real.one_le_rpow hs1.le ha.le
    rw [hmin]
    have h2 : W ^ (η - γ) ≤ W ^ (min α η - γ) := rpow_le_rpow_min hW Pr.W_le_one
    have hX : 0 ≤ Cs * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k)) := by
      positivity
    calc _ ≤ Cs * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          W ^ (η - γ)) * s ^ (-b) := this
      _ ≤ Cs * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          W ^ (min α η - γ)) * s ^ (-b) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0.le _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2
            (Real.rpow_nonneg hd.le _)) (by positivity)
      _ = Cs * Z * s ^ (-b) := by rw [hZ]; ring
      _ ≤ max Cs Cl * Z * s ^ (-b) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hZ0)
            (Real.rpow_nonneg hs0.le _)
      _ = _ := by ring

/-- **The series for the polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`** (singular case,
[Hai14, Prop. 6.16], regular analogue Thm 5.12, (5.44)–(5.50)): for `x, y` in the time slab with
`0 < d = ‖y − x‖_𝔰` and `64 d ≤ W = min (‖x‖_P, ‖y‖_P)`, and `|k|_𝔰 < γ + 2`,
`|∑_n polyUS n| ≤ C K₀ C_f d^{γ+2−|k|} W^{α∧η−γ}`, `K₀ = max(1, C_Γ) C_Π`.  Here `V` is a sector
containing the values of `f`; the hypotheses `hnat` and `hni` are the non-integrality conditions
`γ + 2 − |k| ∉ {|l|_𝔰}` and `|k| ≠ deg i + 2` for `e_i ∈ V ∖ T̄`, `deg i < γ`. -/
theorem exists_abs_tsum_polyUS_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (hN : N' ≤ N) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hαγ : α ≤ γ) (hαη : -2 < min α η)
    (hkγ : (multiDeg k : ℝ) < γ + 2)
    (hnat : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (P : PolynomialSector 𝒯 N') {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hni : ∀ i, i ∉ Set.range P.emb → (Pi.single i 1 : ι → ℝ) ∈ V → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P →
      (∀ z, f z ∈ V) → ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
      0 < parabolicNorm (y - x) →
      64 * parabolicNorm (y - x) ≤
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      Summable (polyUS M h γ f x y k) ∧
      |∑' n, polyUS M h γ f x y k n| ≤
        C * (max 1 CGam * CPi) * Cf * parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
            (min α η - γ) := by
  obtain ⟨a, b, C, ha, hb, hC0, H⟩ := exists_abs_polyUS_le_min_win_near hh hc hN k 𝒯 η α hγ hdeg hαγ hαη
    hkγ hnat P hV hVb hni
  obtain ⟨Cg, hCg0, hCg⟩ := KGammaSup.exists_summable_abs_tsum_le a b ha hb
  refine ⟨Cg * C, mul_nonneg hCg0 hC0,
    fun M f T Cf CPi CGam S hpoly hfV x y hx hy hd hW => ?_⟩
  have Pr : SlabPair T x y := ⟨hx, hy, hd, hW⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hWp := Pr.W_pos
  have hB : 0 ≤ C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ)) := by
    positivity
  obtain ⟨hs, hb'⟩ := hCg _ hd (fun n => polyUS M h γ f x y k n) _ hB
    (fun n => H M f T Cf CPi CGam S hpoly hfV Pr n)
  refine ⟨hs, ?_⟩
  have h1 : |∑' n, polyUS M h γ f x y k n| ≤ ∑' n, |polyUS M h γ f x y k n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  exact h1.trans (hb'.trans (le_of_eq (by ring)))

end Model

end RegularityStructures

end
