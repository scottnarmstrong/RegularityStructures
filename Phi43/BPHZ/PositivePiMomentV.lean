/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaEntryMoments
import Mathlib.Tactic

/-!
# `q`-th moments of `v₂`, `v₃` on `ℝ⁴` (all pairs), without a model

`∫⁻ ‖v_n(proj x, proj y)‖ₑ^q ≤ ofReal (C₀ d(y, x)^s)^q` and the two-scale difference with the
factor `(ε ∨ ε')^θ`, for ALL `x, y : ParabolicSpace`, `d = scaleDist y x`, with `s = 1 - 2κ + κ̄`
(`n = 2`) and `s = 1/2 - 3κ + κ̄` (`n = 3`).  These are the moment bounds for the random `Γ`-entries
`(I(Ψ²)Ψ², Ψ²)`, `(I(Ψ³)Ψ, Ψ)` and `(I(Ψ³)Ψ², Ψ²)`, without the identification with a model.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem lintegral_le_of_le' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {C₀ a b : ℝ} (hC₀ : 0 ≤ C₀) (hab : a ≤ b)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C₀ * a) ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C₀ * b) ^ q :=
  h.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hab hC₀)) q)

/-- **`q`-th moment of `v₂` on `ℝ⁴`, all pairs.** -/
theorem gammaWickSq_lintegral_enorm_pow_le_all (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiSq + κbar)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨Cn, hCn, hn⟩ := gammaWickSq_lintegral_enorm_pow_le_kappa N hρ hk0 (by linarith) hκb0 hκb hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickSq_lintegral_enorm_pow_le_uniform.{u} N hρ hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have hexp : homogeneity κ .iPsiSq + κbar = 1 - 2 * κ.1 + κbar := by
    simp only [homogeneity]
  have he : 0 ≤ homogeneity κ .iPsiSq + κbar := by rw [hexp]; linarith
  have := moment_near_far_bound (P := P)
    (f := fun ω => gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) (q := q)
    (Cn := Cn) (Cf := Cf) (a := 1) (d := parabolicSemigroup.scaleDist y x)
    (e := homogeneity κ .iPsiSq + κbar) hCf zero_le_one he
    (parabolicSemigroup.scaleDist_nonneg y x)
    (fun hd => by
      rw [hexp]
      simpa using lintegral_le_of_le' hCn
        (Real.rpow_le_rpow (torusParabolicSize_nonneg _)
          (torusParabolicSize_spaceTimeProj_sub_le y x) (by linarith : (0 : ℝ) ≤ 1 - 2 * κ.1 + κbar))
        (hn hW hε hξ _ _ ((torusParabolicSize_spaceTimeProj_sub_le y x).trans hd)))
    (by simpa using hf hW hε hξ (spaceTimeProj x) (spaceTimeProj y))
  simpa using this

/-- **`q`-th moment of `v₃` on `ℝ⁴`, all pairs.** -/
theorem gammaWickCube_lintegral_enorm_pow_le_all (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨Cn, hCn, hn⟩ := gammaWickCube_lintegral_enorm_pow_le_kappa N hρ hk0 (by linarith) hκb0 hκb hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickCube_lintegral_enorm_pow_le_uniform.{u} N hρ hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have hexp : homogeneity κ .iPsiCube + κbar = 1 / 2 - 3 * κ.1 + κbar := by
    simp only [homogeneity]
  have he : 0 ≤ homogeneity κ .iPsiCube + κbar := by rw [hexp]; linarith
  have := moment_near_far_bound (P := P)
    (f := fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) (q := q)
    (Cn := Cn) (Cf := Cf) (a := 1) (d := parabolicSemigroup.scaleDist y x)
    (e := homogeneity κ .iPsiCube + κbar) hCf zero_le_one he
    (parabolicSemigroup.scaleDist_nonneg y x)
    (fun hd => by
      rw [hexp]
      simpa using lintegral_le_of_le' hCn
        (Real.rpow_le_rpow (torusParabolicSize_nonneg _)
          (torusParabolicSize_spaceTimeProj_sub_le y x)
          (by linarith : (0 : ℝ) ≤ 1 / 2 - 3 * κ.1 + κbar))
        (hn hW hε hξ _ _ ((torusParabolicSize_spaceTimeProj_sub_le y x).trans hd)))
    (by simpa using hf hW hε hξ (spaceTimeProj x) (spaceTimeProj y))
  simpa using this

/-- **Two-scale difference of `v_n` on `ℝ⁴`, all pairs.** -/
theorem gammaWickSq_sub_lintegral_enorm_pow_le_all (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ)
    (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
            gammaWickSq N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiSq + κbar)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨Cn, hCn, hn⟩ := gammaWickSq_sub_lintegral_enorm_pow_le_kappa N hρ hρ' hk0 (by linarith)
    hκb0 hκb hθ hθκ hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickSq_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ
    (by linarith) hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have hexp : homogeneity κ .iPsiSq + κbar = 1 - 2 * κ.1 + κbar := by
    simp only [homogeneity]
  have he : 0 ≤ homogeneity κ .iPsiSq + κbar := by rw [hexp]; linarith
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hm : 0 ≤ Cn * (max ε ε') ^ θ := mul_nonneg hCn hMx
  have := moment_near_far_bound (P := P)
    (f := fun ω => gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
      gammaWickSq N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) (q := q)
    (Cn := Cn) (Cf := Cf) (a := (max ε ε') ^ θ) (d := parabolicSemigroup.scaleDist y x)
    (e := homogeneity κ .iPsiSq + κbar) hCf hMx he
    (parabolicSemigroup.scaleDist_nonneg y x)
    (fun hd => by
      rw [hexp]
      have h1 := hn hW hε hε' hξ hξ' _ _ ((torusParabolicSize_spaceTimeProj_sub_le y x).trans hd)
      exact lintegral_le_of_le' (C₀ := Cn * (max ε ε') ^ θ) hm
        (Real.rpow_le_rpow (torusParabolicSize_nonneg _)
          (torusParabolicSize_spaceTimeProj_sub_le y x) (by linarith : (0 : ℝ) ≤ 1 - 2 * κ.1 + κbar))
        h1)
    (hf hW hε hε' hξ hξ' (spaceTimeProj x) (spaceTimeProj y))
  exact this

/-- **Two-scale difference of `v_n` on `ℝ⁴`, all pairs.** -/
theorem gammaWickCube_sub_lintegral_enorm_pow_le_all (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ)
    (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
            gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨Cn, hCn, hn⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_kappa N hρ hρ' hk0 (by linarith)
    hκb0 hκb hθ hθκ hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ
    (by linarith) hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have hexp : homogeneity κ .iPsiCube + κbar = 1 / 2 - 3 * κ.1 + κbar := by
    simp only [homogeneity]
  have he : 0 ≤ homogeneity κ .iPsiCube + κbar := by rw [hexp]; linarith
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hm : 0 ≤ Cn * (max ε ε') ^ θ := mul_nonneg hCn hMx
  have := moment_near_far_bound (P := P)
    (f := fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
      gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) (q := q)
    (Cn := Cn) (Cf := Cf) (a := (max ε ε') ^ θ) (d := parabolicSemigroup.scaleDist y x)
    (e := homogeneity κ .iPsiCube + κbar) hCf hMx he
    (parabolicSemigroup.scaleDist_nonneg y x)
    (fun hd => by
      rw [hexp]
      have h1 := hn hW hε hε' hξ hξ' _ _ ((torusParabolicSize_spaceTimeProj_sub_le y x).trans hd)
      exact lintegral_le_of_le' (C₀ := Cn * (max ε ε') ^ θ) hm
        (Real.rpow_le_rpow (torusParabolicSize_nonneg _)
          (torusParabolicSize_spaceTimeProj_sub_le y x) (by linarith : (0 : ℝ) ≤ 1 / 2 - 3 * κ.1 + κbar))
        h1)
    (hf hW hε hε' hξ hξ' (spaceTimeProj x) (spaceTimeProj y))
  exact this
end RegularityStructures.Phi43

end
