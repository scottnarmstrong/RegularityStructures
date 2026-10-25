/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesTaylorWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesZeroWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# The Taylor-remainder kernel at all scales, near-pair `Γ`-bounds

For `0 < d = ‖y − x‖_𝔰 ≤ 2^{-n}` and `g = K^{k,σ}_{n;yx} = dTaylorKernel h k n σ x y`:

* `exists_abs_latticeRecon_dTaylor_all_le_win_near`:
  `|⟨R f, g⟩| ≤ C K₀ C_f d^σ (2^n)^{σ+|k|−2−α∧η}`;
* `exists_abs_pairing_dTaylor_all_le_win_near`: `|⟨Π_x e_i, g⟩| ≤ C K₀ d^σ (2^n)^{σ+|k|−2−deg i}`,
  with `C` independent of `i`.

Here `K₀ = max 1 CGam * CPi`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

/-- Layer bound for the Taylor kernel, all scales. -/
theorem exists_abs_latticeRecon_dTaylor_all_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ)
    (𝒯 : RegularityStructure ι) (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hγ : 0 < γ) (hαγ : α ≤ γ) (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace} (n : ℕ), x.1 ≤ T → y.1 ≤ T →
      0 < parabolicNorm (y - x) → parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      |M.latticeRecon f (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - min α η)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_latticeRecon_dTaylor_le_win_near hh hc k hσ 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨C₀, hC₀, h₀⟩ := exists_abs_latticeRecon_dTaylor_zero_le_win_near hh hc k hσ 𝒯 γ η α hdeg hγ
    hαγ hαη
  refine ⟨max C₁ C₀, hC₁.trans (le_max_left _ _), fun M f T Cf CPi CGam S x y n hx hy hd hdn => ?_⟩
  have hK0 : 0 ≤ (max 1 CGam * CPi) * Cf := by
    exact mul_nonneg S.hK0 S.hCf
  have hdp : 0 ≤ parabolicNorm (y - x) ^ σ := Real.rpow_nonneg (parabolicNorm_nonneg _) _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := h₀ M f T Cf CPi CGam S hx hy hd (by simpa using hdn)
    simp only [pow_zero, Real.one_rpow, mul_one]
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_right (le_max_right C₁ C₀) (mul_nonneg hK0 hdp)
    nlinarith [this]
  · have := h₁ M f T Cf CPi CGam S n hn hx hy hd hdn
    refine this.trans ?_
    have hxm : 0 ≤ parabolicNorm (y - x) ^ σ *
        ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - min α η) := mul_nonneg hdp (by positivity)
    have := mul_le_mul_of_nonneg_right (le_max_left C₁ C₀) (mul_nonneg hK0 hxm)
    nlinarith [this]

/-- Model pairing bound for the Taylor kernel, all scales. -/
theorem exists_abs_pairing_dTaylor_all_le_win_near (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ}
    (hσ : 0 < σ) (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      {x y : ParabolicSpace} (n : ℕ) (i : ι), M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ y.1 → y.1 ≤ 1 → 𝒯.deg i < γ → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i)) := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_pairing_dTaylor_le_win_near hh k hσ 𝒯 hdeg
  have h0 : ∀ i : ι, ∃ C : ℝ, 0 ≤ C ∧ (𝒯.deg i < γ → ∀ (M : Model 𝒯 parabolicSemigroup)
      {CPi CGam : ℝ} {x y : ParabolicSpace},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi →
      M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ y.1 → y.1 ≤ 1 → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ 1 →
      |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) (dTaylorKernel h k 0 σ x y)| ≤
        C * (max 1 CGam * CPi) * parabolicNorm (y - x) ^ σ) := by
    intro i
    by_cases hi : 𝒯.deg i < γ
    · obtain ⟨C, hC, H⟩ := exists_abs_pairing_dTaylor_zero_le_win_near hh k hσ 𝒯 hdeg hi
      exact ⟨C, hC, fun _ => H⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hi⟩
  choose C₀ hC₀ h₀ using h0
  refine ⟨C₁ + ∑ i, C₀ i, add_nonneg hC₁ (Finset.sum_nonneg fun i _ => hC₀ i),
    fun M {CPi CGam x y} n i hPi hCPi hGam hgrowth hx0 hx1 hy0 hy1 hi hd hdn => ?_⟩
  have hK0 : 0 ≤ max 1 CGam * CPi := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  have hdp : 0 ≤ parabolicNorm (y - x) ^ σ := Real.rpow_nonneg (parabolicNorm_nonneg _) _
  have hsum : C₀ i ≤ ∑ j, C₀ j :=
    Finset.single_le_sum (f := C₀) (fun j _ => hC₀ j) (Finset.mem_univ i)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := h₀ i hi M hPi hCPi hGam hgrowth hx0 hx1 hy0 hy1 hd (by simpa using hdn)
    simp only [pow_zero, Real.one_rpow, mul_one]
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_right (hsum.trans (le_add_of_nonneg_left hC₁))
      (mul_nonneg hK0 hdp)
    nlinarith [this]
  · have := h₁ M n i hn hPi hCPi hGam hgrowth hx0 hx1 hi hd hdn
    refine this.trans ?_
    have hxm : 0 ≤ (max 1 CGam * CPi) * (parabolicNorm (y - x) ^ σ *
        ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - 𝒯.deg i)) :=
      mul_nonneg hK0 (mul_nonneg hdp (by positivity))
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
      (Finset.sum_nonneg fun j _ => hC₀ j) : C₁ ≤ C₁ + ∑ j, C₀ j) hxm
    nlinarith [this]

end Model

end RegularityStructures

end
