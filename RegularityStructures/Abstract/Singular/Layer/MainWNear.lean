/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.FirstLevelWNear
public import RegularityStructures.Abstract.Singular.Layer.IncrementWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Abstract.Singular.Layer.Geometry
public import RegularityStructures.Abstract.Singular.Layer.Main
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The layer bound for the lattice reconstruction, near-pair `Γ`-bounds

[Hai14, Proposition 6.9], lattice form: for `f ∈ D^{γ,η}_P` with values in a sector of regularity
`α`, `α ∧ η > -2`, and a test function `ψ = φ^λ_x` (for any `x`, in particular crossing
`P = {t = 0}`) vanishing after time `T ≤ 1`, the lattice approximations `S_n f ψ` converge and
`|⟨R f, ψ⟩| ≤ C (max 1 CGam * CPi) Cf λ^{α ∧ η}`
(`exists_tendsto_latticeApprox_abs_latticeRecon_le_win_near`). The model bounds are assumed on
`hairerTimeWindow`, together with a qualitative growth model that does not enter `C`, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Layer bound** (Hairer, arXiv:1303.5113v4, Prop. 6.9, lattice form). -/
theorem exists_tendsto_latticeApprox_abs_latticeRecon_le_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 →
      (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f →
      (∀ z, z ∉ timeSlab T → f z = 0) → (∀ z i, f z i ≠ 0 → α ≤ 𝒯.deg i) → 0 ≤ Cf →
      ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 →
      ∀ (x : ParabolicSpace),
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) →
      Tendsto (M.latticeApprox f (rescaledTestFunction φ lam x)) atTop
        (𝓝 (M.latticeRecon f (rescaledTestFunction φ lam x))) ∧
      |M.latticeRecon f (rescaledTestFunction φ lam x)| ≤
        C * (max 1 CGam * CPi) * Cf * lam ^ (min α η) := by
  obtain ⟨g, hg0, hgγ, hgη, hmg⟩ := Layer.exists_gamma_prime hγ hαγ hαη
  obtain ⟨Cinc, hCinc, hinc⟩ := exists_abs_layerApprox_succ_sub_le_win_near 𝒯 γ g η hgγ hgη
  obtain ⟨Cfirst, hCfirst, hfirst⟩ := exists_abs_layerApprox_le_win_near 𝒯 γ α η
  set m : ℝ := min α η with hm_def
  have hm2 : 0 < 2 + m := by linarith
  set q₁ : ℝ := ((2 : ℝ)⁻¹) ^ g with hq₁_def
  set q₂ : ℝ := ((2 : ℝ)⁻¹) ^ (2 + m) with hq₂_def
  have hq₁0 : 0 ≤ q₁ := Real.rpow_nonneg (by norm_num) _
  have hq₂0 : 0 ≤ q₂ := Real.rpow_nonneg (by norm_num) _
  have hq₁1 : q₁ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hg0
  have hq₂1 : q₂ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hm2
  have h1q₁ : 0 < 1 - q₁ := by linarith
  have h1q₂ : 0 < 1 - q₂ := by linarith
  refine ⟨Cfirst + Cinc * (1 / (1 - q₁) + 1 / (1 - q₂)), by positivity, ?_⟩
  intro M f T Cf CPi CGam hPi hCPi hGam hgrowth hT1 hfT hf hf0 hα hCf φ hφ lam hlam hlam1 x hφT
  have S : LayerSettingWNear M f γ η α Cf CPi CGam T :=
    ⟨hγ, hPi, hCPi, hGam, hgrowth, hT1, hdeg, hfT, hf, hf0, hα, hαγ, hαη, hCf⟩
  obtain ⟨n₀, hn₁, hn₂⟩ := Layer.exists_nat_scale hlam hlam1
  set ψ := rescaledTestFunction φ lam x with hψ_def
  set r₀ : ℝ := ((2 : ℝ) ^ n₀)⁻¹ with hr₀_def
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n₀ := by positivity
  have hr₀ : 0 < r₀ := by positivity
  have hr₀lam : r₀ ≤ lam := by
    rw [hr₀_def, inv_le_iff_one_le_mul₀ h2]; nlinarith
  set θ : ℝ := max (-(η - g)) 0 with hθ_def
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  set a : ℕ → ℝ := fun j => M.latticeApprox f ψ (j + n₀) with ha_def
  set A₁ : ℝ := Cinc * (max 1 CGam * CPi) * Cf * lam ^ (-θ) * r₀ ^ g with hA₁
  set A₂ : ℝ := Cinc * (max 1 CGam * CPi) * Cf * lam ^ (-2 : ℝ) * r₀ ^ (2 + m) with hA₂
  have hstep : ∀ j, |a (j + 1) - a j| ≤ A₁ * q₁ ^ j + A₂ * q₂ ^ j := by
    intro j
    have hn32 : 32 * ((2 : ℝ) ^ (j + n₀))⁻¹ ≤ lam := by
      have h2j : (2 : ℝ) ^ n₀ ≤ 2 ^ (j + n₀) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : 32 < lam * 2 ^ (j + n₀) :=
        lt_of_lt_of_le hn₁ (mul_le_mul_of_nonneg_left h2j hlam.le)
      have h4 : (0 : ℝ) < (2 : ℝ) ^ (j + n₀) := by positivity
      rw [← div_eq_mul_inv, div_le_iff₀ h4]
      linarith
    have := hinc S hφ hlam hlam1 hφT hn32
    have e : j + 1 + n₀ = (j + n₀) + 1 := by omega
    show |M.latticeApprox f ψ (j + 1 + n₀) - M.latticeApprox f ψ (j + n₀)| ≤ _
    rw [e]
    refine this.trans (le_of_eq ?_)
    rw [Layer.rpow_inv_two_pow_add, Layer.rpow_inv_two_pow_add]
    rw [hA₁, hA₂, hq₁_def, hq₂_def]
    ring
  obtain ⟨L, hL, hLb⟩ := Layer.exists_tendsto_of_abs_sub_le hq₁0 hq₁1 hq₂0 hq₂1 hstep
  have hS : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat n₀).1 hL
  refine ⟨?_, ?_⟩
  · rw [show M.latticeRecon f ψ = L from hS.limUnder_eq]
    exact hS
  · rw [show M.latticeRecon f ψ = L from hS.limUnder_eq]
    have h0 : |a 0| ≤ Cfirst * (max 1 CGam * CPi) * Cf * lam ^ m := by
      have := hfirst S hφ hlam hlam1 x (n := n₀) hn₁.le hn₂
      simpa [ha_def] using this
    have hlamm : 0 ≤ lam ^ m := Real.rpow_nonneg hlam.le _
    have hA₁le : A₁ ≤ Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) := by
      have e1 : r₀ ^ g ≤ lam ^ g := Real.rpow_le_rpow hr₀.le hr₀lam hg0.le
      have e2 : m ≤ -θ + g := by
        rcases le_total (-(η - g)) 0 with h | h
        · rw [hθ_def, max_eq_right h]; linarith
        · rw [hθ_def, max_eq_left h]; linarith [min_le_right α η]
      have e3 : lam ^ (-θ) * lam ^ g ≤ lam ^ m := by
        rw [← Real.rpow_add hlam]
        exact Real.rpow_le_rpow_of_exponent_ge hlam hlam1 e2
      have e4 : lam ^ (-θ) * r₀ ^ g ≤ lam ^ m :=
        (mul_le_mul_of_nonneg_left e1 (Real.rpow_nonneg hlam.le _)).trans e3
      have hc : 0 ≤ Cinc * (max 1 CGam * CPi) * Cf := by
        have := hCf; positivity
      calc A₁ = (Cinc * (max 1 CGam * CPi) * Cf) * (lam ^ (-θ) * r₀ ^ g) := by rw [hA₁]; ring
        _ ≤ (Cinc * (max 1 CGam * CPi) * Cf) * lam ^ m := mul_le_mul_of_nonneg_left e4 hc
        _ = _ := by ring
    have hA₂le : A₂ ≤ Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) := by
      have e1 : r₀ ^ (2 + m) ≤ lam ^ (2 + m) := Real.rpow_le_rpow hr₀.le hr₀lam hm2.le
      have e3 : lam ^ (-2 : ℝ) * lam ^ (2 + m) = lam ^ m := by
        rw [← Real.rpow_add hlam]; congr 1; ring
      have e4 : lam ^ (-2 : ℝ) * r₀ ^ (2 + m) ≤ lam ^ m :=
        ((mul_le_mul_of_nonneg_left e1 (Real.rpow_nonneg hlam.le _))).trans e3.le
      have hc : 0 ≤ Cinc * (max 1 CGam * CPi) * Cf := by
        have := hCf; positivity
      calc A₂ = (Cinc * (max 1 CGam * CPi) * Cf) * (lam ^ (-2 : ℝ) * r₀ ^ (2 + m)) := by
            rw [hA₂]; ring
        _ ≤ (Cinc * (max 1 CGam * CPi) * Cf) * lam ^ m := mul_le_mul_of_nonneg_left e4 hc
        _ = _ := by ring
    have hsplit : |L| ≤ |a 0| + |L - a 0| := by
      calc |L| = |a 0 + (L - a 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hd1 : A₁ / (1 - q₁) ≤ Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) / (1 - q₁) :=
      div_le_div_of_nonneg_right hA₁le h1q₁.le
    have hd2 : A₂ / (1 - q₂) ≤ Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) / (1 - q₂) :=
      div_le_div_of_nonneg_right hA₂le h1q₂.le
    calc |L| ≤ |a 0| + |L - a 0| := hsplit
      _ ≤ Cfirst * (max 1 CGam * CPi) * Cf * lam ^ m + (A₁ / (1 - q₁) + A₂ / (1 - q₂)) :=
          add_le_add h0 hLb
      _ ≤ Cfirst * (max 1 CGam * CPi) * Cf * lam ^ m +
          (Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) / (1 - q₁) +
            Cinc * ((max 1 CGam * CPi) * Cf * lam ^ m) / (1 - q₂)) := by gcongr
      _ = _ := by field_simp

end RegularityStructures

end
