/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Window.LocalOrderNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.GeneratorProps
public import RegularityStructures.Analysis.Semigroup.Locality.PairingUniform

/-!
# Off-centre model bounds, near-pair `Γ`-bounds

The local order `|(Q_u Π_x e_i)(y)| ≤ |ι| max(1, C_Γ) C_Π ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`
for `x, y` in the window, and the off-centre bound: for `x` in the window and a centre `z` with
`0 ≤ z₀ ≤ 1`, `‖z − x‖ ≤ 3`, `⟨Π_x e_i, φ^1_z⟩` is the limit of `∫ Q_s Π_x e_i φ^1_z` and both are
bounded by `C K₀`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- **Local order at a point of the window**: for `x, y ∈ S`, `0 < u ≤ 1`,
`|(Q_u Π_x e_i)(y)| ≤ |ι| max(1, C_Γ) C_Π ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`. -/
theorem abs_regPi_single_le_of_mem_win_near {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {K : RegularisingSemigroup E μ} (M : Model 𝒯 K) {γ CPi CGam : ℝ} {S : Set E}
    (hPi : M.PiBoundOn γ CPi S) (hCPi : 0 ≤ CPi) (hGam : M.GammaNearOn γ CGam S) {i : ι}
    (hi : 𝒯.deg i < γ) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : K.scaleDist y x ≤ gammaNearRadius) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    |M.regPi x (Pi.single i 1) u y| ≤ Fintype.card ι * (max 1 CGam * CPi) *
      ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i), u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
  have hC1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
  set T := Finset.univ.filter (fun j => 𝒯.deg j ≤ 𝒯.deg i) with hT
  set h : ℝ → ℝ := fun a =>
    max 1 CGam * CPi * (u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a)) with hh
  have hh0 : ∀ a ∈ T.image 𝒯.deg, 0 ≤ h a := fun a _ =>
    mul_nonneg (mul_nonneg hC1 hCPi)
      (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
  calc |M.regPi x (Pi.single i 1) u y|
      = |∑ j, M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| := by
        rw [← M.regPi_gammaMap y x, M.regPi_eq_sum]
    _ ≤ ∑ j, |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, if 𝒯.deg j ≤ 𝒯.deg i then h (𝒯.deg j) else 0 :=
        Finset.sum_le_sum fun j _ => M.abs_gammaMap_mul_regPi_le_of_mem_near hPi hCPi hGam hi hu hx hy hxy j
    _ = ∑ j ∈ T, h (𝒯.deg j) := by rw [hT, Finset.sum_filter]
    _ ≤ Fintype.card ι * ∑ a ∈ T.image 𝒯.deg, h a := sum_le_card_mul_sum_image 𝒯 T hh0
    _ = Fintype.card ι * (max 1 CGam * CPi) * ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i),
          u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
        rw [RegularityStructure.degreesAtMost, ← hT, hh, ← Finset.mul_sum]
        ring

/-- Off-centre window model bound: for `x` in the window and a centre `z` with `0 ≤ z₀ ≤ 1`,
`‖z − x‖ ≤ 3`: `∫ Q_s Π_x e_i φ^1_z → ⟨Π_x e_i, φ^1_z⟩`, `|⟨Π_x e_i, φ^1_z⟩| ≤ C K₀`, and
`|∫ Q_s Π_x e_i φ^1_z| ≤ C K₀` for `0 < s < 1`. -/
theorem exists_abs_pairing_regPi_single_offcentre_le_win_near (𝒯 : RegularityStructure ι)
    {γ : ℝ} (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι} (hi : 𝒯.deg i < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ} {x z : ParabolicSpace},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow → M.HasQualitativeGrowthAt γ x →
      x ∈ hairerTimeWindow → 0 ≤ z.1 → z.1 ≤ 1 → parabolicNorm (z - x) ≤ 3 →
      ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 →
      Tendsto (fun s => ∫ y, M.regPi x (Pi.single i 1) s y * rescaledTestFunction φ 1 z y)
        (𝓝[>] 0) (𝓝 (parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
          (rescaledTestFunction φ 1 z))) ∧
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (rescaledTestFunction φ 1 z)| ≤
        C * (max 1 CGam * CPi) ∧
      ∀ s ∈ Set.Ioo (0 : ℝ) 1,
        |∫ y, M.regPi x (Pi.single i 1) s y * rescaledTestFunction φ 1 z y| ≤
          C * (max 1 CGam * CPi) := by
  classical
  set A := 𝒯.degreesAtMost (𝒯.deg i) with hA
  have hmemA : ∀ a ∈ A, ∃ j, 𝒯.deg j < γ ∧ 𝒯.deg j = a ∧ a ≤ 𝒯.deg i := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesAtMost).1 ha
    exact ⟨j, hj.trans_lt hi, rfl, hj⟩
  have hAne : A.Nonempty := ⟨𝒯.deg i, (𝒯.mem_degreesAtMost).2 ⟨i, le_rfl, rfl⟩⟩
  set a₀ := A.min' hAne with ha₀
  have hAmem : ∀ a ∈ A, a₀ ≤ a ∧ a ≤ 𝒯.deg i ∧ -4 < a := by
    intro a ha
    obtain ⟨j, hj, rfl, hle⟩ := hmemA a ha
    exact ⟨A.min'_le _ ha, hle, hdeg j hj⟩
  have ha₀A : a₀ ∈ A := A.min'_mem hAne
  have ha₀4 : -4 < a₀ := (hAmem a₀ ha₀A).2.2
  have hq : 0 ≤ 𝒯.deg i - a₀ := sub_nonneg.2 (hAmem a₀ ha₀A).2.1
  set q := 𝒯.deg i - a₀ with hqdef
  have hord : parabolicSemigroup.order = 4 := rfl
  set C₁ : ℝ := Fintype.card ι * A.card * 4 ^ q with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set Bg : ℝ := 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff) with hBg
  have hBg0 : 0 ≤ Bg := by
    have := generatorTimeCoeff_pos
    have := generatorSpaceCoeff_pos
    positivity
  have hpc : 0 ≤ parabolicSemigroup.pairingConst ({a₀} : Finset ℝ) := by
    unfold RegularisingSemigroup.pairingConst
    rw [Finset.sum_singleton, hord]
    have : 0 < a₀ + 4 := by linarith
    positivity
  refine ⟨C₁ * parabolicSemigroup.pairingConst ({a₀} : Finset ℝ) * (16 + Bg), by positivity,
    fun M {CPi CGam x z} hPi hCPi hGam hgrowth hx hz0 hz1 hzx {φ} hφ => ?_⟩
  set K0 : ℝ := max 1 CGam * CPi with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  obtain ⟨C', β, q', hC'0, hq'0, hcr⟩ := hgrowth.exists_crude
  -- the crude bound, centred at `z`
  have hcrude : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, |M.regPi x (Pi.single i 1) u y| ≤
      (C' * 4 ^ q') * u ^ (β / parabolicSemigroup.order) *
        (1 + parabolicSemigroup.scaleDist y z) ^ q' := by
    intro u hu y
    refine (hcr i hi u hu y).trans ?_
    have hs0 : 0 ≤ parabolicNorm (y - z) := parabolicNorm_nonneg _
    have hle : 1 + parabolicNorm (y - x) ≤ 4 * (1 + parabolicNorm (y - z)) := by
      have e : y - x = (y - z) + (z - x) := by abel
      have := parabolicNorm_add_le (y - z) (z - x)
      rw [← e] at this
      linarith
    have h1 : (1 + parabolicNorm (y - x)) ^ q' ≤ 4 ^ q' * (1 + parabolicNorm (y - z)) ^ q' := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith [parabolicNorm_nonneg (y - x)]) hle hq'0
    have hu0 : 0 ≤ u ^ (β / parabolicSemigroup.order) := Real.rpow_nonneg hu.1.le _
    calc C' * u ^ (β / parabolicSemigroup.order) * (1 + parabolicNorm (y - x)) ^ q'
        ≤ C' * u ^ (β / parabolicSemigroup.order) *
          (4 ^ q' * (1 + parabolicNorm (y - z)) ^ q') :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hC'0 hu0)
      _ = _ := by
          change _ = _ * (1 + parabolicNorm (y - z)) ^ q'
          ring
  have hloc : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, parabolicSemigroup.scaleDist y z ≤ 1 →
      |M.regPi x (Pi.single i 1) u y| ≤ (C₁ * K0) * ∑ a ∈ ({a₀} : Finset ℝ),
        u ^ (a / parabolicSemigroup.order) * parabolicSemigroup.scaleDist y z ^ (a₀ - a) := by
    intro u hu y hy
    rw [Finset.sum_singleton, sub_self, Real.rpow_zero, mul_one]
    have hyw : y ∈ hairerTimeWindow := ball_subset_hairerTimeWindow hz0 hz1 hy
    set d := parabolicSemigroup.scaleDist y x with hdd
    have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg _ _
    have hd4 : d ≤ 4 := by
      have h1 : d = parabolicNorm (y - x) := rfl
      have h2 : parabolicNorm (y - z) ≤ 1 := hy
      have e : y - x = (y - z) + (z - x) := by abel
      have := parabolicNorm_add_le (y - z) (z - x)
      rw [← e] at this
      rw [h1]; linarith
    refine (M.abs_regPi_single_le_of_mem_win_near hPi hCPi hGam hi hx hyw
      (by unfold gammaNearRadius; exact hd4) hu).trans ?_
    have hterm : ∀ a ∈ A, u ^ (a / parabolicSemigroup.order) * d ^ (𝒯.deg i - a) ≤
        u ^ (a₀ / parabolicSemigroup.order) * 4 ^ q := by
      intro a ha
      obtain ⟨h1, h2, -⟩ := hAmem a ha
      have hu1 : u ^ (a / parabolicSemigroup.order) ≤ u ^ (a₀ / parabolicSemigroup.order) :=
        Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2
          (div_le_div_of_nonneg_right h1 (by rw [hord]; norm_num))
      have hd1 : d ^ (𝒯.deg i - a) ≤ 4 ^ q := by
        calc _ ≤ (4 : ℝ) ^ (𝒯.deg i - a) := Real.rpow_le_rpow hd0 hd4 (sub_nonneg.2 h2)
          _ ≤ 4 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hqdef]; linarith)
      exact mul_le_mul hu1 hd1 (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hu.1.le _)
    have hsum : ∑ a ∈ A, u ^ (a / parabolicSemigroup.order) * d ^ (𝒯.deg i - a) ≤
        A.card * (u ^ (a₀ / parabolicSemigroup.order) * 4 ^ q) := by
      have := Finset.sum_le_card_nsmul A _ _ hterm
      rwa [nsmul_eq_mul] at this
    calc Fintype.card ι * (max 1 CGam * CPi) * ∑ a ∈ A,
          u ^ (a / parabolicSemigroup.order) * d ^ (𝒯.deg i - a)
        ≤ Fintype.card ι * K0 * (A.card * (u ^ (a₀ / parabolicSemigroup.order) * 4 ^ q)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by rw [hC₁]; ring
  have hlam : (0 : ℝ) < 1 := one_pos
  have hgen := isGeneratorPair_rescaledTestFunction hφ hlam z
  have hψ1 := integral_abs_parabolicGenerator_rescaledTestFunction_le hφ hlam z
  rw [Real.one_rpow] at hψ1
  obtain ⟨L, hL, hLb, hLu⟩ := RegularisingSemigroup.exists_tendsto_abs_le_uniform_of_local
    parabolicSemigroup_isSymmetric parabolicSemigroup_isMetricScale
    parabolicSemigroup_isJointMeasurable (M.regPi_mem x _)
    (fun _ hu => M.measurable_regPi x _ hu) (x₀ := z) (γ := a₀) (q := q') (C' := C' * 4 ^ q')
    (β := β) (R := 1) (A := {a₀}) (B₀ := 16) (fun a ha => by
      rw [Finset.mem_singleton] at ha; subst ha; exact ⟨by rw [hord]; linarith, le_rfl⟩)
    (mul_nonneg hC₁0 hK00) (by positivity) hq'0 hloc hcrude hlam le_rfl le_rfl
    (measurable_rescaledTestFunction hφ 1 z)
    (measurable_parabolicGenerator_rescaledTestFunction hφ 1 z)
    (integrable_rescaledTestFunction hφ hlam z)
    (integrable_parabolicGenerator_rescaledTestFunction hφ hlam z)
    (fun y hy => rescaledTestFunction_eq_zero hφ.2.1 hlam hy)
    (fun y hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hlam hy)
    (integral_abs_rescaledTestFunction_le hφ hlam z)
    (B₁ := Bg) (by rw [hord, Real.one_rpow, mul_one, hBg]; simpa using hψ1) hgen
  have hp := parabolicSemigroup.pairing_eq_of_tendsto hL
  have hfin : C₁ * K0 * parabolicSemigroup.pairingConst ({a₀} : Finset ℝ) * (16 + Bg) *
      (1 : ℝ) ^ a₀ = C₁ * parabolicSemigroup.pairingConst ({a₀} : Finset ℝ) * (16 + Bg) * K0 := by
    rw [Real.one_rpow]; ring
  refine ⟨by rw [hp]; exact hL, ?_, fun s hs => ?_⟩
  · rw [hp]; exact hLb.trans (le_of_eq hfin)
  · refine (hLu s ?_).trans (le_of_eq hfin)
    rwa [hord, Real.one_rpow]

end Model

end RegularityStructures

end
