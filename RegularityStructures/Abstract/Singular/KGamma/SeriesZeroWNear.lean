/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesZeroW
public import RegularityStructures.Abstract.Singular.KGamma.Radius2WNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesOffCentreWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesTaylorWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.KGamma.SeriesZeroW`

The statements of `RegularityStructures.Abstract.Singular.KGamma.SeriesZeroW` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

/-- Layer bound for the Taylor kernel at scale `0`, window models:
`|⟨R f, K^{k,σ}_{0;yx}⟩| ≤ C K₀ C_f d^σ`. -/
theorem exists_abs_latticeRecon_dTaylor_zero_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ)
    (𝒯 : RegularityStructure ι) (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hγ : 0 < γ) (hαγ : α ≤ γ) (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, x.1 ≤ T → y.1 ≤ T →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ 1 →
      |M.latticeRecon f (dTaylorKernel h k 0 σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * parabolicNorm (y - x) ^ σ := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_deriv_bound_win_near 𝒯 γ η α hdeg hγ
    hαγ hαη
  obtain ⟨Cd, hCd, H⟩ := exists_dTaylor_zero_data hh k hσ
  refine ⟨Cl * Cd, by positivity, fun M f T Cf CPi CGam S x y hx hy hd hd1 => ?_⟩
  obtain ⟨hcd, hsupp, hder⟩ := H x y hd hd1
  have hE : 0 < Cd * parabolicNorm (y - x) ^ σ := by positivity
  obtain ⟨_, hb⟩ := hCl M f T Cf CPi CGam S hE hcd hsupp hder
    (fun w hw => dTaylorKernel_eq_zero_of_lt hh.contDiff hc k 0 σ hx hy w hw)
  refine hb.trans (le_of_eq ?_)
  ring

end Model

namespace Model

/-- Model pairing bound for the Taylor kernel at scale `0`, window models:
`|⟨Π_x e_i, K^{k,σ}_{0;yx}⟩| ≤ C K₀ d^σ` for `x`, `y` with `0 ≤ x₀, y₀ ≤ 1`. -/
theorem exists_abs_pairing_dTaylor_zero_le_win_near (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ)
    {σ : ℝ} (hσ : 0 < σ) (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ} {x y : ParabolicSpace},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ y.1 → y.1 ≤ 1 →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ 1 →
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (dTaylorKernel h k 0 σ x y)| ≤
        C * (max 1 CGam * CPi) * parabolicNorm (y - x) ^ σ := by
  classical
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_pairing_regPi_single_offcentre_le_win_near 𝒯 hdeg hi
  obtain ⟨E, hEσ, hE⟩ := exists_abs_taylorProfile_le_sup_on σ
  set g : ParabolicSpace → ℝ := lineIter (multiDirs k) h with hgdef
  have hg : ContDiff ℝ ∞ g := contDiff_lineIter hh.contDiff _
  have hg0 : ∀ w, 1 < parabolicNorm w → g w = 0 := fun w hw =>
    lineIter_eq_zero_of_lt hh.eq_zero _ hw
  have hgc : HasCompactSupport g := hasCompactSupport_of_eq_zero_unit hg0
  have hword : ∀ ℓ : List (Fin 4), ∃ A : ℝ, 0 < A ∧ ∀ z,
      IsScaledTest (fun y => lineIter (ℓ.map coordDir) g (z - y)) z 1 A := by
    intro ℓ
    refine exists_isScaledTest_unit_of_contDiff (contDiff_lineIter hg _) (fun w hw => ?_)
    rw [hgdef, ← lineIter_append]
    exact lineIter_eq_zero_of_lt hh.eq_zero _ hw
  choose A hA0 hA using hword
  set S0 : ℝ := (E.map fun ℓ => A ℓ * C₀).sum with hS0
  have hS0nn : 0 ≤ S0 := List.sum_nonneg fun t ht => by
    obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 ht
    exact mul_nonneg (hA0 ℓ).le hC₀0
  refine ⟨S0, hS0nn, ?_⟩
  intro M CPi CGam x y hPi hCPi hGam hgrowth hx0 hx1 hy0 hy1 hd hd1
  have hgx := M.hasQualitativeGrowthAt_of_exists hgrowth x
  have hxw : x ∈ hairerTimeWindow := ⟨by linarith, by linarith⟩
  set d := parabolicNorm (y - x) with hddef
  set K0 : ℝ := max 1 CGam * CPi with hK0
  have hK0nn : 0 ≤ K0 := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  obtain ⟨C', β, q', hC'0, hq'0, hcr⟩ := hgx.exists_crude
  have hΛint : ∀ s ∈ Set.Ioc (0 : ℝ) 1, LocallyIntegrable (M.regPi x (Pi.single i 1) s) :=
    fun s hs => locallyIntegrable_of_polyGrowth (M.measurable_regPi x _ hs.1) (x := x)
      (C := C' * s ^ (β / 4)) hq'0 (fun w => hcr i hi s hs w)
  -- regularised pairings against the derivatives of the kernel centred in the slab
  have hpair : ∀ (ℓ : List (Fin 4)) (z : ParabolicSpace), 0 ≤ z.1 → z.1 ≤ 1 →
      parabolicNorm (z - x) ≤ 3 →
      (∃ L : ℝ, Tendsto (fun s => ∫ w, M.regPi x (Pi.single i 1) s w *
        lineIter (ℓ.map coordDir) g (z - w)) (𝓝[>] 0) (𝓝 L)) ∧
      ∀ s ∈ Set.Ioo (0 : ℝ) 1, |∫ w, M.regPi x (Pi.single i 1) s w *
        lineIter (ℓ.map coordDir) g (z - w)| ≤ A ℓ * (C₀ * K0) := by
    intro ℓ z hz0 hz1 hzx
    obtain ⟨φ, hφ, hφeq⟩ := (hA ℓ z).exists_eq_smul
    obtain ⟨hT, -, hLu⟩ := hC₀ M hPi hCPi hGam hgx hxw hz0 hz1 hzx hφ
    have hint : ∀ s, ∫ w, M.regPi x (Pi.single i 1) s w * lineIter (ℓ.map coordDir) g (z - w) =
        (A ℓ * 1 ^ 5) * ∫ w, M.regPi x (Pi.single i 1) s w * rescaledTestFunction φ 1 z w := by
      intro s
      rw [← integral_const_mul]
      congr 1; funext w
      have := congrFun hφeq w
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this]; ring
    refine ⟨⟨_, (hT.const_mul (A ℓ * 1 ^ 5)).congr (fun s => (hint s).symm)⟩, fun s hs => ?_⟩
    rw [hint s, abs_mul, abs_of_pos (by have := hA0 ℓ; positivity)]
    have := hLu s hs
    calc A ℓ * 1 ^ 5 * |∫ w, M.regPi x (Pi.single i 1) s w * rescaledTestFunction φ 1 z w|
        ≤ A ℓ * 1 ^ 5 * (C₀ * K0) := mul_le_mul_of_nonneg_left this (by have := hA0 ℓ; positivity)
      _ = _ := by ring
  have he1 : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∫ w, M.regPi x (Pi.single i 1) s w *
      dTaylorKernel h k 0 σ x y w = taylorProfile (fun z => ∫ w, M.regPi x (Pi.single i 1) s w *
        g (z - w)) σ (y - x) x := by
    intro s hs
    have eψ : ∀ w, dTaylorKernel h k 0 σ x y w = taylorProfile g σ (y - x) (x - w) := by
      intro w
      rw [dTaylorKernel_eq_profile hh.contDiff]
      simp [parabolicDilate_one, hgdef]
    simp only [eψ]
    exact integral_mul_taylorProfile (hΛint s hs) hg hgc σ x y
  -- the uniform bound
  have hkey : ∀ s ∈ Set.Ioo (0 : ℝ) 1, |∫ w, M.regPi x (Pi.single i 1) s w *
      dTaylorKernel h k 0 σ x y w| ≤ S0 * K0 * d ^ σ := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hΛ := hΛint s hs'
    rw [he1 s hs']
    have hGs : ContDiff ℝ ∞ (fun z => ∫ w, M.regPi x (Pi.single i 1) s w * g (z - w)) :=
      contDiff_integral_mul_sub hΛ hg hgc
    set R : Set ParabolicSpace := {v | 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ parabolicNorm (v - x) ≤ 3} with hR
    have hB : ∀ ℓ u, u ∈ R → |lineIter (ℓ.map coordDir)
        (fun z => ∫ w, M.regPi x (Pi.single i 1) s w * g (z - w)) u| ≤ A ℓ * (C₀ * K0) := by
      intro ℓ u hu
      rw [lineIter_integral_mul_sub hΛ hg hgc]
      exact (hpair ℓ u hu.1 hu.2.1 hu.2.2).2 s hs
    have hbox : ∀ τ : Fin 4 → ℝ, (∀ j, 0 ≤ τ j ∧ τ j ≤ 1) →
        x + boxPt (parabolicCoords (y - x)) τ ∈ R := by
      intro τ hτ
      have hfst : (x + boxPt (parabolicCoords (y - x)) τ).1 = x.1 + τ 0 * (y.1 - x.1) := by
        simp [boxPt_fst, parabolicCoords]
      obtain ⟨ht0, ht1⟩ := hτ 0
      refine ⟨?_, ?_, ?_⟩
      · rw [hfst]; nlinarith
      · rw [hfst]; nlinarith
      · rw [add_sub_cancel_left]
        exact (parabolicNorm_boxPt_le (y - x) hτ).trans (by linarith)
    have hmain := hE hGs (fun ℓ => A ℓ * (C₀ * K0)) hB (y - x) x d hd.le
      (fun i => abs_parabolicCoords_le i) hbox
    refine hmain.trans ?_
    have hdσ : ∀ ℓ ∈ E, d ^ indexWeight ℓ ≤ d ^ σ := by
      intro ℓ hℓ
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hd.le hd1 hσ.le (hEσ ℓ hℓ)
    calc (E.map fun ℓ => d ^ indexWeight ℓ * (A ℓ * (C₀ * K0))).sum
        ≤ (E.map fun ℓ => d ^ σ * K0 * (A ℓ * C₀)).sum := by
          refine List.sum_le_sum fun ℓ hℓ => ?_
          have h1 := hA0 ℓ
          calc d ^ indexWeight ℓ * (A ℓ * (C₀ * K0)) ≤ d ^ σ * (A ℓ * (C₀ * K0)) :=
                mul_le_mul_of_nonneg_right (hdσ ℓ hℓ) (by positivity)
            _ = _ := by ring
      _ = S0 * K0 * d ^ σ := by
          rw [List.sum_map_mul_left, hS0]; ring
  -- the limit
  have hlimI : ∃ L : ℝ, Tendsto (fun s => ∫ w, M.regPi x (Pi.single i 1) s w *
      dTaylorKernel h k 0 σ x y w) (𝓝[>] 0) (𝓝 L) := by
    obtain ⟨Ly, hLy⟩ := (hpair [] y hy0 hy1 (hd1.trans (by norm_num))).1
    have hlx : ∀ l : Fin 4 →₀ ℕ, ∃ L : ℝ, Tendsto (fun s => ∫ w, M.regPi x (Pi.single i 1) s w *
        lineIter ((Finsupp.toMultiset l).toList.map coordDir) g (x - w)) (𝓝[>] 0) (𝓝 L) :=
      fun l => (hpair _ x hx0 hx1 (by rw [sub_self]; simp [parabolicNorm])).1
    choose Lx hLx using hlx
    refine ⟨Ly - ∑ l ∈ taylorIdx σ, (evalParabolic (MvPolynomial.monomial l 1) (y - x) /
      multiFact l) * Lx l, ?_⟩
    have hsum := hLy.sub (tendsto_finsetSum (taylorIdx σ) fun l _ => (hLx l).const_mul
      (evalParabolic (MvPolynomial.monomial l 1) (y - x) / multiFact l))
    refine hsum.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    have hΛ := hΛint s hs
    rw [he1 s hs]
    unfold taylorProfile
    simp only [lineIter_integral_mul_sub hΛ hg hgc]
    rw [show x + (y - x) = y by abel]
    simp only [List.map_nil, lineIter_nil, multiDirs]
  obtain ⟨L, hL⟩ := hlimI
  rw [parabolicSemigroup.pairing_eq_of_tendsto hL]
  exact le_of_tendsto hL.abs (Filter.mem_of_superset (Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1))
    hkey)

end Model

end RegularityStructures

end
