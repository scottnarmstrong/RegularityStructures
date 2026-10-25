/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullGap
public import Phi43.BPHZ.GammaFullParam
public import Phi43.BPHZ.GammaFullMinkowski
import Mathlib.Tactic

/-!
# Moments of the five parameters of `Γ_{yx}` for the canonical model

For `g ω = gammaFullParam N κ C (ξ ω) y x` and `d = d(y, x)`, `0 ≤ κ̄ ≤ κ/2`, the `q`-th moments are
bounded by (constant independent of `ε, x, y`):

* `g.cPsiGrad k`: `d^(1/2 - κ + κ̄)`;
* `g.cPsi`: `d^(3/2 - κ + κ̄)` (it is `-v₁ - ∑ₖ gₖ rₖ` with `|rₖ| ≤ d`);
* `g.cPsiSq`: `d^(1 - 2κ + κ̄)`, `g.cPsiCube`: `d^(1/2 - 3κ + κ̄)`;
* `g.cPsiCube²`: `d^(1 - 6κ + κ̄)`: for `d ≤ 1` from the `2q`-th moment of `v₃` since
  `d^(1 - 6κ + 2κ̄) ≤ d^(1 - 6κ + κ̄)`, for `d ≥ 1` from the uniform `2q`-th moment.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem lintegral_enorm_sq_pow_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : Ω → ℝ)
    (q : ℕ) : ∫⁻ ω, ‖f ω * f ω‖ₑ ^ q ∂P = ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P := by
  refine lintegral_congr fun ω => ?_
  rw [enorm_mul, mul_pow, two_mul, pow_add]

theorem ofReal_pow_two_mul {a : ℝ} (ha : 0 ≤ a) (q : ℕ) :
    ENNReal.ofReal a ^ (2 * q) = ENNReal.ofReal (a * a) ^ q := by
  rw [ENNReal.ofReal_mul ha, two_mul, pow_add, mul_pow]

/-- **The square of a variable with a `2q`-th moment bound**: near `d ≤ 1` the exponent doubles
(`d^(2e) ≤ d^e'` for `e' ≤ 2e`), far it is bounded uniformly (`d^e' ≥ 1`). -/
theorem gammaFull_sq_gap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q : ℕ}
    {Cn Cf d e e' : ℝ} (hCn : 0 ≤ Cn) (hCf : 0 ≤ Cf) (hd : 0 ≤ d) (he : 0 < e) (he' : 0 ≤ e')
    (hee : e' ≤ 2 * e)
    (hnear : d ≤ 1 → ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (Cn * d ^ e) ^ (2 * q))
    (hfar : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal Cf ^ (2 * q)) :
    ∫⁻ ω, ‖f ω * f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (max (Cn * Cn) (Cf * Cf) * d ^ e') ^ q := by
  rw [lintegral_enorm_sq_pow_eq]
  have hde : 0 ≤ d ^ e' := Real.rpow_nonneg hd _
  rcases le_or_gt d 1 with h1 | h1
  · have h := hnear h1
    rw [ofReal_pow_two_mul (mul_nonneg hCn (Real.rpow_nonneg hd _))] at h
    refine le_ofReal_pow_mono h ?_
    have e2 : d ^ e * d ^ e = d ^ (2 * e) := by
      rw [two_mul, Real.rpow_add' hd (by linarith)]
    have hle : d ^ (2 * e) ≤ d ^ e' := by
      rcases hd.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        exact Real.rpow_nonneg le_rfl _
      · exact Real.rpow_le_rpow_of_exponent_ge h0 h1 hee
    calc Cn * d ^ e * (Cn * d ^ e) = Cn * Cn * d ^ (2 * e) := by rw [← e2]; ring
      _ ≤ Cn * Cn * d ^ e' := mul_le_mul_of_nonneg_left hle (mul_nonneg hCn hCn)
      _ ≤ max (Cn * Cn) (Cf * Cf) * d ^ e' :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hde
  · have hge : 1 ≤ d ^ e' := Real.one_le_rpow h1.le he'
    refine le_ofReal_pow_mono (by rw [ofReal_pow_two_mul hCf] at hfar; exact hfar) ?_
    calc Cf * Cf ≤ max (Cn * Cn) (Cf * Cf) := le_max_right _ _
      _ = max (Cn * Cn) (Cf * Cf) * 1 := (mul_one _).symm
      _ ≤ max (Cn * Cn) (Cf * Cf) * d ^ e' :=
        mul_le_mul_of_nonneg_left hge ((mul_nonneg hCn hCn).trans (le_max_left _ _))

theorem measurable_gammaGrad_omega {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (i : Fin 3) (x y : SpaceTime) :
    Measurable fun ω => gammaGrad N ξ i x y ω := by
  have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    (measurable_hairerGradIncrementKernel N i x y)
  unfold gammaGrad
  simpa using this

theorem measurable_gammaPsiTaylor_omega {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) :
    Measurable fun ω => gammaPsiTaylor N ξ x t a ω := by
  have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    (measurable_hairerTaylorKernel N x t a)
  unfold gammaPsiTaylor
  simpa using this

private theorem kappa_pos3 (κ : Kappa) : 0 < κ.1 := κ.2.1
private theorem kappa_lt3 (κ : Kappa) : κ.1 < 1 / 16 := κ.2.2

/-- **`cPsi = -v₁ - ∑ gₖ rₖ` has the moment at the gap exponent `3/2 - κ + κ̄`.** -/
theorem gammaFull_cPsi_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {C : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsi‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^ (3 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos3 κ
  have hk1 := kappa_lt3 κ
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_gap_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  obtain ⟨Cg, hCg, hg⟩ := gammaGrad_gap_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  refine ⟨C1 + 3 * Cg, by positivity, ?_⟩
  intro Ω _ P W ε ξ C hW hε hξ x y
  have := hW.isProbabilityMeasure
  set d := parabolicSemigroup.scaleDist y x with hd
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
  have hdd : ∀ k : Fin 3, d * d ^ (1 / 2 - κ.1 + κbar) = d ^ (3 / 2 - κ.1 + κbar) := fun k => by
    rcases hd0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, Real.zero_rpow (by linarith)]
    · rw [← Real.rpow_one_add' hd0 (by linarith)]
      congr 1; ring
  have e : ∀ ω, (gammaFullParam N κ C (ξ ω) y x).cPsi =
      -(gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω +
        (CanonicalData.relCoord y x (0 : Fin 3).succ *
            gammaGrad N ξ 0 (spaceTimeProj x) (spaceTimeProj y) ω +
          CanonicalData.relCoord y x (1 : Fin 3).succ *
            gammaGrad N ξ 1 (spaceTimeProj x) (spaceTimeProj y) ω +
          CanonicalData.relCoord y x (2 : Fin 3).succ *
            gammaGrad N ξ 2 (spaceTimeProj x) (spaceTimeProj y) ω)) := fun ω => by
    rw [gammaFullParam_cPsi (hξ.1 ω), Fin.sum_univ_three]
    ring
  have hgk : ∀ k : Fin 3, ∫⁻ ω, ‖CanonicalData.relCoord y x k.succ *
      gammaGrad N ξ k (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cg * d ^ (3 / 2 - κ.1 + κbar)) ^ q := fun k => by
    refine le_ofReal_pow_mono (lintegral_enorm_pow_const_mul_le _ (hg hW hε hξ k x y)) ?_
    have hr := abs_relCoord_succ_le y x k
    have hde : 0 ≤ d ^ (1 / 2 - κ.1 + κbar) := Real.rpow_nonneg hd0 _
    calc |CanonicalData.relCoord y x k.succ| * (Cg * d ^ (1 / 2 - κ.1 + κbar))
        ≤ d * (Cg * d ^ (1 / 2 - κ.1 + κbar)) :=
          mul_le_mul_of_nonneg_right hr (mul_nonneg hCg hde)
      _ = Cg * (d * d ^ (1 / 2 - κ.1 + κbar)) := by ring
      _ = Cg * d ^ (3 / 2 - κ.1 + κbar) := by rw [hdd k]
  have hmk : ∀ k : Fin 3, Measurable fun ω => CanonicalData.relCoord y x k.succ *
      gammaGrad N ξ k (spaceTimeProj x) (spaceTimeProj y) ω := fun k =>
    (measurable_gammaGrad_omega N hξ k _ _).const_mul _
  have hS := lintegral_enorm_pow_add_le hq
    (((hmk 0).add (hmk 1)).aestronglyMeasurable) (hmk 2).aestronglyMeasurable
    (lintegral_enorm_pow_add_le hq (hmk 0).aestronglyMeasurable (hmk 1).aestronglyMeasurable
      (hgk 0) (hgk 1) (mul_nonneg hCg (Real.rpow_nonneg hd0 _))
      (mul_nonneg hCg (Real.rpow_nonneg hd0 _))) (hgk 2)
    (add_nonneg (mul_nonneg hCg (Real.rpow_nonneg hd0 _)) (mul_nonneg hCg (Real.rpow_nonneg hd0 _)))
    (mul_nonneg hCg (Real.rpow_nonneg hd0 _))
  have hV := h1 hW hε hξ x y
  have hsum := lintegral_enorm_pow_add_le hq (measurable_gammaPsiTaylor_omega N hξ _ _ _).aestronglyMeasurable
    ((((hmk 0).add (hmk 1)).add (hmk 2)).aestronglyMeasurable) hV hS
    (mul_nonneg hC1 (Real.rpow_nonneg hd0 _))
    (add_nonneg (add_nonneg (mul_nonneg hCg (Real.rpow_nonneg hd0 _))
      (mul_nonneg hCg (Real.rpow_nonneg hd0 _))) (mul_nonneg hCg (Real.rpow_nonneg hd0 _)))
  simp_rw [e, enorm_neg]
  refine le_ofReal_pow_mono hsum ?_
  generalize d ^ (3 / 2 - κ.1 + κbar) = D
  nlinarith [mul_nonneg hC1 (le_refl 0), hC1, hCg]

/-- **`cPsiGrad k = g_k` has the moment at the gap exponent `1/2 - κ + κ̄`.** -/
theorem gammaFull_cPsiGrad_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {C : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (k : Fin 3) (x y : ParabolicSpace),
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiGrad k‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^ (1 / 2 - κ.1 + κbar)) ^ q := by
  obtain ⟨Cg, hCg, hg⟩ := gammaGrad_gap_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  refine ⟨Cg, hCg, ?_⟩
  intro Ω _ P W ε ξ C hW hε hξ k x y
  simp only [gammaFullParam_cPsiGrad (hξ.1 _)]
  exact hg hW hε hξ k x y

/-- **`cPsiSq = v₂` has the moment at the gap exponent `1 - 2κ + κ̄`.** -/
theorem gammaFull_cPsiSq_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {C : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiSq‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^ (1 - 2 * κ.1 + κbar)) ^ q := by
  obtain ⟨Cs, hCs, hs⟩ := gammaWickSq_gap_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  refine ⟨Cs, hCs, ?_⟩
  intro Ω _ P W ε ξ C hW hε hξ hgr x y
  simp only [gammaFullParam_cPsiSq (ρ := ρ) (ε := ε) (hξ.1 _) (hgr _)]
  exact hs hW hε hξ x y

end RegularityStructures.Phi43

end
