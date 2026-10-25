/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullUniform
public import Phi43.BPHZ.GammaFullMinkowski
public import Phi43.BPHZ.GammaEntryMoments
public import Phi43.BPHZ.GammaMomentDiffAll
public import Phi43.BPHZ.PositiveMomentGammaMoment
import Mathlib.Tactic

/-!
# The `q`-th moments of `v₂`, `v₃`, `g_i` at the gap exponent, for all `x, y : ParabolicSpace`

With `d = parabolicSemigroup.scaleDist y x`, `κ ∈ (0, 1/16)` and `0 ≤ κ̄ ≤ κ/2`, for all
`x, y : ParabolicSpace` and `ε ∈ (0, 1]` (constants independent of `ε, x, y`):

* `∫⁻ ‖v₂‖ₑ^q ≤ ofReal (C d^(1 - 2κ + κ̄))^q`, `∫⁻ ‖v₃‖ₑ^q ≤ ofReal (C d^(1/2 - 3κ + κ̄))^q`,
  `∫⁻ ‖g_i‖ₑ^q ≤ ofReal (C d^(1/2 - κ + κ̄))^q`;
* the two-scale differences, with the factor `(ε ∨ ε')^θ`, `0 < θ < κ - κ̄`.

The near bound (`d ≤ 1`) is the one of `GammaMoment*`; the far bound is the uniform bound
(`Phi43.BPHZ.GammaMomentUniformLp`, `Phi43.BPHZ.GammaFullUniform`), and `d^e ≥ 1` for `d ≥ 1`
(`moment_near_far_bound`). Here `v₂ = gammaWickSq N ρ ε ξ x' y'`, `g_i = gammaGrad N ξ i x' y'` with
`x' = proj x`, `y' = proj y`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Passing from the torus size of the projected increment to `d(y, x)`. -/
theorem gammaFull_rpow_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q : ℕ}
    {Cn M t d e : ℝ} (hCM : 0 ≤ Cn * M) (ht : t ≤ d) (ht0 : 0 ≤ t) (he : 0 ≤ e)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cn * M * t ^ e) ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cn * M * d ^ e) ^ q :=
  lintegral_enorm_pow_mono h (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 ht he) hCM)

/-- **Near/far combination for a bound in the torus size `t ≤ d`.** -/
theorem gammaFull_gap_of_near {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {Cn Cf M t d e : ℝ} (hCn : 0 ≤ Cn) (hCf : 0 ≤ Cf) (hM : 0 ≤ M) (he : 0 ≤ e)
    (ht : t ≤ d) (ht0 : 0 ≤ t)
    (hnear : t ≤ 1 → ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cn * M * t ^ e) ^ q)
    (hfar : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cf * M) ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (max Cn Cf * M * d ^ e) ^ q :=
  moment_near_far_bound hCf hM he (ht0.trans ht) (fun hd =>
    lintegral_enorm_pow_mono (hnear (ht.trans hd)) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ht0 ht he) (mul_nonneg hCn hM))) hfar

private theorem kappa_pos'' (κ : Kappa) : 0 < κ.1 := κ.2.1
private theorem kappa_lt'' (κ : Kappa) : κ.1 < 1 / 16 := κ.2.2

/-- **`v₂`, all `x, y`.** -/
theorem gammaWickSq_gap_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^ (1 - 2 * κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  obtain ⟨Cn, hCn, hn⟩ := gammaWickSq_lintegral_enorm_pow_le_kappa N hρ hk0 (by linarith) hκb0 hκb hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickSq_lintegral_enorm_pow_le_uniform.{u} N hρ hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have h := gammaFull_gap_of_near (P := P)
    (f := fun ω => gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) (M := 1)
    (e := 1 - 2 * κ.1 + κbar) hCn hCf zero_le_one (by linarith)
    (torusParabolicSize_spaceTimeProj_sub_le y x) (torusParabolicSize_nonneg _)
    (fun h1 => by simpa using hn hW hε hξ _ _ h1)
    (by simpa using hf hW hε hξ (spaceTimeProj x) (spaceTimeProj y))
  simpa using h

/-- **`g_i`, all `x, y`** (the constant is uniform in `i`). -/
theorem gammaGrad_gap_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (i : Fin 3) (x y : ParabolicSpace),
        ∫⁻ ω, ‖gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
            (1 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  have hnear : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ (1 / 2 - κ.1 + κbar)) ^ q :=
    fun i => gammaGrad_lintegral_enorm_pow_le_kappa N hρ i hk0 (by linarith) hκb0 hκb hq
  choose Cn hCn hn using hnear
  obtain ⟨Cf, hCf, hf⟩ := gammaGrad_lintegral_enorm_pow_le_uniform.{u} N hρ hq
  set Cm : ℝ := max (max (Cn 0) (Cn 1)) (Cn 2) with hCm
  have hle : ∀ i, Cn i ≤ Cm := fun i => by
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  refine ⟨max Cm Cf, le_max_of_le_left ((hCn 0).trans (hle 0)), ?_⟩
  intro Ω _ P W ε ξ hW hε hξ i x y
  have := hW.isProbabilityMeasure
  have h := gammaFull_gap_of_near (P := P)
    (f := fun ω => gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω) (M := 1)
    (e := 1 / 2 - κ.1 + κbar) ((hCn i).trans (hle i)) hCf zero_le_one (by linarith)
    (torusParabolicSize_spaceTimeProj_sub_le y x) (torusParabolicSize_nonneg _)
    (fun h1 => by
      have := hn i hW hε hξ _ _ h1
      simpa using lintegral_enorm_pow_mono (a := Cn i * 1 * torusParabolicSize
        (spaceTimeProj y - spaceTimeProj x) ^ (1 / 2 - κ.1 + κbar)) (b := Cm * 1 *
        torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ^ (1 / 2 - κ.1 + κbar))
        (by simpa using this)
        (mul_le_mul_of_nonneg_right (by simpa using hle i)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
    (by simpa using hf hW hε hξ i (spaceTimeProj x) (spaceTimeProj y))
  simpa using h

/-- **`v₂^ε - v₂^ε'`, all `x, y`.** -/
theorem gammaWickSq_sub_gap_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
            gammaWickSq N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (1 - 2 * κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  obtain ⟨Cn, hCn, hn⟩ := gammaWickSq_sub_lintegral_enorm_pow_le_kappa N hρ hρ' hk0 (by linarith)
    hκb0 hκb hθ hθκ hq
  obtain ⟨Cf, hCf, hf⟩ := gammaWickSq_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ
    (by linarith) hq
  refine ⟨max Cn Cf, le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  exact gammaFull_gap_of_near (P := P) hCn hCf
    (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _) (by linarith)
    (torusParabolicSize_spaceTimeProj_sub_le y x) (torusParabolicSize_nonneg _)
    (fun h1 => hn hW hε hε' hξ hξ' _ _ h1)
    (hf hW hε hε' hξ hξ' (spaceTimeProj x) (spaceTimeProj y))

/-- **`g_i^ε - g_i^ε'`, all `x, y`** (the constant is uniform in `i`). -/
theorem gammaGrad_sub_gap_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (i : Fin 3) (x y : ParabolicSpace),
        ∫⁻ ω, ‖gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω -
            gammaGrad N ξ' i (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (1 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  have hnear : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ (1 / 2 - κ.1 + κbar)) ^ q :=
    fun i => gammaGrad_sub_lintegral_enorm_pow_le_kappa N hρ hρ' i (by linarith) hκb0 hθ hθκ hq
  choose Cn hCn hn using hnear
  obtain ⟨Cf, hCf, hf⟩ := gammaGrad_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ
    (by linarith) hq
  set Cm : ℝ := max (max (Cn 0) (Cn 1)) (Cn 2) with hCm
  have hle : ∀ i, Cn i ≤ Cm := fun i => by
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  refine ⟨max Cm Cf, le_max_of_le_left ((hCn 0).trans (hle 0)), ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' i x y
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  exact gammaFull_gap_of_near (P := P) ((hCn i).trans (hle i)) hCf hMx (by linarith)
    (torusParabolicSize_spaceTimeProj_sub_le y x) (torusParabolicSize_nonneg _)
    (fun h1 => lintegral_enorm_pow_mono (hn i hW hε hε' hξ hξ' _ _ h1)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle i) hMx)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
    (hf hW hε hε' hξ hξ' i (spaceTimeProj x) (spaceTimeProj y))

theorem one_add_le_eight_mul_rpow {d e : ℝ} (hd : 1 / 2 ≤ d) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    1 + d ≤ 8 * d ^ e := by
  have hd0 : 0 < d := by linarith
  rcases le_or_gt 1 d with h1 | h1
  · have h := Real.rpow_le_rpow_of_exponent_le h1 he1
    rw [Real.rpow_one] at h
    linarith
  · have h := Real.rpow_le_rpow_of_exponent_ge hd0 h1.le he2
    have h2 : (1 / 4 : ℝ) ≤ d ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith
    linarith

/-- **Near/far combination for `v₁`** (threshold `1/2`; the far bound has linear growth). -/
theorem gammaFull_gap_of_near_half {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {Cn Cf M d e : ℝ} (hCf : 0 ≤ Cf) (hM : 0 ≤ M) (he1 : 1 ≤ e)
    (he2 : e ≤ 2) (hd : 0 ≤ d)
    (hnear : d ≤ 1 / 2 → ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cn * M * d ^ e) ^ q)
    (hfar : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cf * M * (1 + d)) ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (max Cn (8 * Cf) * M * d ^ e) ^ q := by
  rcases le_or_gt d (1 / 2) with h | h
  · refine lintegral_enorm_pow_mono (hnear h) ?_
    have : Cn ≤ max Cn (8 * Cf) := le_max_left _ _
    have hde : 0 ≤ d ^ e := Real.rpow_nonneg hd _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hM) hde
  · refine lintegral_enorm_pow_mono hfar ?_
    have h8 := one_add_le_eight_mul_rpow h.le he1 he2
    have hde : 0 ≤ d ^ e := Real.rpow_nonneg hd _
    have : 8 * Cf ≤ max Cn (8 * Cf) := le_max_right _ _
    calc Cf * M * (1 + d) ≤ Cf * M * (8 * d ^ e) := mul_le_mul_of_nonneg_left h8 (mul_nonneg hCf hM)
      _ = (8 * Cf) * M * d ^ e := by ring
      _ ≤ max Cn (8 * Cf) * M * d ^ e :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hM) hde

theorem abs_snd_le_parabolicNorm (t : ℝ) (a : Fin 3 → ℝ) (i : Fin 3) :
    |a i| ≤ parabolicNorm (t, a) := by
  have := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  have h3 := Real.sqrt_nonneg |t|
  unfold parabolicNorm
  simp only
  linarith

theorem parabolicNorm_sub_prod (y x : ParabolicSpace) :
    parabolicNorm (x.1 - y.1, x.2 - y.2) = parabolicSemigroup.scaleDist y x := by
  change parabolicNorm (x - y) = parabolicNorm (y - x)
  exact parabolicNorm_sub_comm x y

/-- **`v₁` at the recentred point, all `x, y`.** -/
theorem gammaPsiTaylor_gap_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
            (3 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  obtain ⟨Cn, hCn, hn⟩ := gammaPsiTaylor_lintegral_enorm_pow_le_kappa N hρ hk0 (by linarith) hκb0 hκb hq
  obtain ⟨Cf, hCf, hf⟩ := gammaPsiTaylor_lintegral_enorm_pow_le_uniform.{u} N hρ hq
  refine ⟨max Cn (8 * Cf), le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  have h := gammaFull_gap_of_near_half (P := P)
    (f := fun ω => gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω) (M := 1)
    (e := 3 / 2 - κ.1 + κbar) hCf zero_le_one (by linarith) (by linarith) hd0
    (fun h1 => by
      rw [← parabolicNorm_sub_prod y x] at h1 ⊢
      simpa using hn hW hε hξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) h1)
    (by
      have := hf hW hε hξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2)
        (parabolicSemigroup.scaleDist y x) hd0 (fun i => by
          rw [← parabolicNorm_sub_prod y x]
          exact abs_snd_le_parabolicNorm _ _ i)
      simpa using this)
  simpa using h

/-- **`v₁^ε - v₁^ε'` at the recentred point, all `x, y`.** -/
theorem gammaPsiTaylor_sub_gap_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω -
            gammaPsiTaylor N ξ' (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (3 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos'' κ
  have hk1 := kappa_lt'' κ
  obtain ⟨Cn, hCn, hn⟩ := gammaPsiTaylor_sub_lintegral_enorm_pow_le_kappa N hρ hρ' (by linarith)
    hκb0 hθ hθκ hq
  obtain ⟨Cf, hCf, hf⟩ := gammaPsiTaylor_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ
    (by linarith) hq
  refine ⟨max Cn (8 * Cf), le_max_of_le_left hCn, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  exact gammaFull_gap_of_near_half (P := P) hCf (Real.rpow_nonneg
    (le_max_of_le_left hε.1.le) _) (by linarith) (by linarith) hd0
    (fun h1 => by
      rw [← parabolicNorm_sub_prod y x] at h1 ⊢
      exact hn hW hε hε' hξ hξ' (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) h1)
    (by
      have := hf hW hε hε' hξ hξ' (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2)
        (parabolicSemigroup.scaleDist y x) hd0 (fun i => by
          rw [← parabolicNorm_sub_prod y x]
          exact abs_snd_le_parabolicNorm _ _ i)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this)

end RegularityStructures.Phi43

end
