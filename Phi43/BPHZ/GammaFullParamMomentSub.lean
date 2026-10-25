/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullParamMoment
import Mathlib.Tactic

/-!
# Moments of the differences of the parameters of `Γ_{yx}` of two canonical models

For two regularised noises `ξ` (mollifier `ρ`, scale `ε`, constants `C`) and `ξ'` (`ρ'`, `ε'`, `C'`),
`P ω = gammaFullParam N κ C (ξ ω) y x`, `P' ω = gammaFullParam N κ C' (ξ' ω) y x`,
`0 < θ < κ - κ̄`, `0 ≤ κ̄`, and `M = (ε ∨ ε')^θ`: the `q`-th moments of

* `cPsiGrad k`: `P - P'` is bounded by `C₀ M d^(1/2 - κ + κ̄)`;
* `cPsi`: `C₀ M d^(3/2 - κ + κ̄)`;
* `cPsiSq`: `C₀ M d^(1 - 2κ + κ̄)`, `cPsiCube`: `C₀ M d^(1/2 - 3κ + κ̄)`;
* `cPsiCube²`: `C₀ M d^(1 - 6κ + κ̄)`: `a² - b² = (a - b)(a + b)` and Cauchy–Schwarz through the
  `2q`-th moments of `a - b` (near: `M d^(1/2 - 3κ + κ̄)`, far: `M`) and `a + b`
  (near: `d^(1/2 - 3κ + κ̄)`, far: bounded).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem measurable_gammaWickCube_omega {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    Measurable fun ω => gammaWickCube N ρ ε ξ x y ω :=
  measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
    (measurable_hairerI2Psi2Kernel N x y)

/-- **Product of two variables with `2q`-th moment bounds** (near: exponent `e` each, far: uniform). -/
theorem gammaFull_prod_gap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) {q : ℕ}
    {A A' B B' M d e e' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hd : 0 ≤ d) (he : 0 < e) (he' : 0 ≤ e') (hee : e' ≤ 2 * e)
    (hfn : d ≤ 1 → ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (A * M * d ^ e) ^ (2 * q))
    (hff : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (A' * M) ^ (2 * q))
    (hgn : d ≤ 1 → ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (B * d ^ e) ^ (2 * q))
    (hgf : ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal B' ^ (2 * q)) :
    ∫⁻ ω, ‖f ω * g ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max (A * B) (A' * B') * M * d ^ e') ^ q := by
  have hde : 0 ≤ d ^ e' := Real.rpow_nonneg hd _
  rcases le_or_gt d 1 with h1 | h1
  · have h := lintegral_enorm_pow_mul_le hf hg (hfn h1) (hgn h1)
      (mul_nonneg (mul_nonneg hA hM) (Real.rpow_nonneg hd _))
    refine le_ofReal_pow_mono h ?_
    have e2 : d ^ e * d ^ e = d ^ (2 * e) := by
      rw [two_mul, Real.rpow_add' hd (by linarith)]
    have hle : d ^ (2 * e) ≤ d ^ e' := by
      rcases hd.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        exact Real.rpow_nonneg le_rfl _
      · exact Real.rpow_le_rpow_of_exponent_ge h0 h1 hee
    calc A * M * d ^ e * (B * d ^ e) = A * B * M * d ^ (2 * e) := by rw [← e2]; ring
      _ ≤ A * B * M * d ^ e' :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg (mul_nonneg hA hB) hM)
      _ ≤ max (A * B) (A' * B') * M * d ^ e' :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) hde
  · have hge : 1 ≤ d ^ e' := Real.one_le_rpow h1.le he'
    have h := lintegral_enorm_pow_mul_le hf hg hff hgf (mul_nonneg hA' hM)
    refine le_ofReal_pow_mono h ?_
    calc A' * M * B' = A' * B' * M * 1 := by ring
      _ ≤ max (A * B) (A' * B') * M * 1 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
          zero_le_one
      _ ≤ max (A * B) (A' * B') * M * d ^ e' :=
        mul_le_mul_of_nonneg_left hge (mul_nonneg ((mul_nonneg hA hB).trans (le_max_left _ _)) hM)

private theorem kappa_pos5 (κ : Kappa) : 0 < κ.1 := κ.2.1
private theorem kappa_lt5 (κ : Kappa) : κ.1 < 1 / 16 := κ.2.2

/-- **`cPsiGrad k - cPsiGrad' k`.** -/
theorem gammaFull_cPsiGrad_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {C C' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (k : Fin 3) (x y : ParabolicSpace),
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiGrad k -
            (gammaFullParam N κ C' (ξ' ω) y x).cPsiGrad k‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (1 / 2 - κ.1 + κbar)) ^ q := by
  obtain ⟨Cg, hCg, hg⟩ := gammaGrad_sub_gap_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  refine ⟨Cg, hCg, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' C C' hW hε hε' hξ hξ' k x y
  simp only [gammaFullParam_cPsiGrad (hξ.1 _), gammaFullParam_cPsiGrad (hξ'.1 _)]
  exact hg hW hε hε' hξ hξ' k x y

/-- **`cPsiSq - cPsiSq'`.** -/
theorem gammaFull_cPsiSq_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {C C' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiSq -
            (gammaFullParam N κ C' (ξ' ω) y x).cPsiSq‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (1 - 2 * κ.1 + κbar)) ^ q := by
  obtain ⟨Cs, hCs, hs⟩ := gammaWickSq_sub_gap_lintegral_le N hρ hρ' hκb0 hκb hθ hθκ hq (κ := κ)
  refine ⟨Cs, hCs, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' C C' hW hε hε' hξ hξ' hgr hgr' x y
  simp only [gammaFullParam_cPsiSq (ρ := ρ) (ε := ε) (hξ.1 _) (hgr _),
    gammaFullParam_cPsiSq (ρ := ρ') (ε := ε') (hξ'.1 _) (hgr' _)]
  exact hs hW hε hε' hξ hξ' x y

/-- **`cPsi - cPsi'`.** -/
theorem gammaFull_cPsi_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {C C' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsi -
            (gammaFullParam N κ C' (ξ' ω) y x).cPsi‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
            (3 / 2 - κ.1 + κbar)) ^ q := by
  have hk0 := kappa_pos5 κ
  have hk1 := kappa_lt5 κ
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_sub_gap_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  obtain ⟨Cg, hCg, hg⟩ := gammaGrad_sub_gap_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  refine ⟨C1 + 3 * Cg, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' C C' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  set d := parabolicSemigroup.scaleDist y x with hd
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hdd : d * d ^ (1 / 2 - κ.1 + κbar) = d ^ (3 / 2 - κ.1 + κbar) := by
    rcases hd0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, Real.zero_rpow (by linarith)]
    · rw [← Real.rpow_one_add' hd0 (by linarith)]
      congr 1; ring
  have hreg : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → ∀ (k : Fin 3), Measurable fun ω =>
        gammaGrad N ξ₀ k (spaceTimeProj x) (spaceTimeProj y) ω := by
    intro ξ₀ h k
    rcases h with h | h <;> exact measurable_gammaGrad_omega N h k _ _
  have hreg1 : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → Measurable fun ω =>
        gammaPsiTaylor N ξ₀ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω := by
    intro ξ₀ h
    rcases h with h | h <;> exact measurable_gammaPsiTaylor_omega N h _ _ _
  have e : ∀ ω, (gammaFullParam N κ C (ξ ω) y x).cPsi - (gammaFullParam N κ C' (ξ' ω) y x).cPsi =
      -((gammaPsiTaylor N ξ (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω -
          gammaPsiTaylor N ξ' (spaceTimeProj y) (x.1 - y.1) (x.2 - y.2) ω) +
        (CanonicalData.relCoord y x (0 : Fin 3).succ *
            (gammaGrad N ξ 0 (spaceTimeProj x) (spaceTimeProj y) ω -
              gammaGrad N ξ' 0 (spaceTimeProj x) (spaceTimeProj y) ω) +
          CanonicalData.relCoord y x (1 : Fin 3).succ *
            (gammaGrad N ξ 1 (spaceTimeProj x) (spaceTimeProj y) ω -
              gammaGrad N ξ' 1 (spaceTimeProj x) (spaceTimeProj y) ω) +
          CanonicalData.relCoord y x (2 : Fin 3).succ *
            (gammaGrad N ξ 2 (spaceTimeProj x) (spaceTimeProj y) ω -
              gammaGrad N ξ' 2 (spaceTimeProj x) (spaceTimeProj y) ω))) := fun ω => by
    rw [gammaFullParam_cPsi (hξ.1 ω), gammaFullParam_cPsi (hξ'.1 ω), Fin.sum_univ_three,
      Fin.sum_univ_three]
    ring
  have hgk : ∀ k : Fin 3, ∫⁻ ω, ‖CanonicalData.relCoord y x k.succ *
      (gammaGrad N ξ k (spaceTimeProj x) (spaceTimeProj y) ω -
        gammaGrad N ξ' k (spaceTimeProj x) (spaceTimeProj y) ω)‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cg * (max ε ε') ^ θ * d ^ (3 / 2 - κ.1 + κbar)) ^ q := fun k => by
    refine le_ofReal_pow_mono (lintegral_enorm_pow_const_mul_le _ (hg hW hε hε' hξ hξ' k x y)) ?_
    have hr := abs_relCoord_succ_le y x k
    have hde : 0 ≤ d ^ (1 / 2 - κ.1 + κbar) := Real.rpow_nonneg hd0 _
    calc |CanonicalData.relCoord y x k.succ| * (Cg * (max ε ε') ^ θ * d ^ (1 / 2 - κ.1 + κbar))
        ≤ d * (Cg * (max ε ε') ^ θ * d ^ (1 / 2 - κ.1 + κbar)) :=
          mul_le_mul_of_nonneg_right hr (mul_nonneg (mul_nonneg hCg hMx) hde)
      _ = Cg * (max ε ε') ^ θ * (d * d ^ (1 / 2 - κ.1 + κbar)) := by ring
      _ = Cg * (max ε ε') ^ θ * d ^ (3 / 2 - κ.1 + κbar) := by rw [hdd]
  have hmk : ∀ k : Fin 3, Measurable fun ω => CanonicalData.relCoord y x k.succ *
      (gammaGrad N ξ k (spaceTimeProj x) (spaceTimeProj y) ω -
        gammaGrad N ξ' k (spaceTimeProj x) (spaceTimeProj y) ω) := fun k =>
    (((hreg ξ (Or.inl hξ) k).sub (hreg ξ' (Or.inr hξ') k))).const_mul _
  have hDnn : 0 ≤ Cg * (max ε ε') ^ θ * d ^ (3 / 2 - κ.1 + κbar) :=
    mul_nonneg (mul_nonneg hCg hMx) (Real.rpow_nonneg hd0 _)
  have hS := lintegral_enorm_pow_add_le hq
    (((hmk 0).add (hmk 1)).aestronglyMeasurable) (hmk 2).aestronglyMeasurable
    (lintegral_enorm_pow_add_le hq (hmk 0).aestronglyMeasurable (hmk 1).aestronglyMeasurable
      (hgk 0) (hgk 1) hDnn hDnn) (hgk 2) (add_nonneg hDnn hDnn) hDnn
  have hV := h1 hW hε hε' hξ hξ' x y
  have hsum := lintegral_enorm_pow_add_le hq
    (((hreg1 ξ (Or.inl hξ)).sub (hreg1 ξ' (Or.inr hξ'))).aestronglyMeasurable)
    ((((hmk 0).add (hmk 1)).add (hmk 2)).aestronglyMeasurable) hV hS
    (mul_nonneg (mul_nonneg hC1 hMx) (Real.rpow_nonneg hd0 _))
    (add_nonneg (add_nonneg hDnn hDnn) hDnn)
  simp_rw [e, enorm_neg]
  refine le_ofReal_pow_mono hsum ?_
  generalize d ^ (3 / 2 - κ.1 + κbar) = D
  generalize (max ε ε') ^ θ = M
  exact le_of_eq (by ring)

end RegularityStructures.Phi43

end
