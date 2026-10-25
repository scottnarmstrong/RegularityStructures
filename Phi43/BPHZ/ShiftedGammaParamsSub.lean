/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaParams
public import Phi43.BPHZ.ShiftedGammaCubeSub
public import Phi43.BPHZ.ShiftedGammaEntrySub
import Mathlib.Tactic

/-!
# Entry difference moments of the shifted `Γ`-parameters, two models

With `M = (ε ∨ ε')^θ + |s - s'|`, the differences of the parameters `cPsi`, `cPsiGrad`, `cPsiSq`
have the unshifted bounds (with `(ε ∨ ε')^θ ≤ M`), `cPsiCube` has the near/far bounds of
`gammaFull_cPsiCubeShift_sub_near_far`, and `cPsiCube² - cPsiCube'²` follows by
`(U - U')(U + U')` and `gammaFull_prod_gap`.  The result
(`gammaFull_entryShift_sub_lintegral_le`) is the moment of every random entry difference.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem sgp_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q : ℕ}
    {a M0 M D : ℝ} (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a * M0 * D) ^ q)
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hM : M0 ≤ M) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a * M * D) ^ q :=
  le_ofReal_pow_mono h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM ha) hD)

/-- **Moments of the differences of the random `Γ`-entries of two models with shifted
constants.** -/
theorem gammaFull_entryShift_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {C C' : RenormalisationConstants} {s s' : ℝ}, |s| ≤ B → |s'| ≤ B →
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      C₁ C = hairerWickConstant N ρ ε + s → C₁ C' = hairerWickConstant N ρ' ε' + s' →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ i j : Symbol, IsGammaFullRandom i → j ≠ i → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖structureGroupMap (gammaFullParam N κ C (ξ ω) y x) (basis i) j -
            structureGroupMap (gammaFullParam N κ C' (ξ' ω) y x) (basis i) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * ((max ε ε') ^ θ + |s - s'|) * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ i - homogeneity κ j + κbar)) ^ q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  have hθκ' : θ ≤ κ.1 := by linarith
  have hq2 : 1 ≤ 2 * q := by omega
  obtain ⟨C1, hC1, h1⟩ := gammaFull_cPsi_sub_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  obtain ⟨Cg, hCg, hg⟩ := gammaFull_cPsiGrad_sub_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  obtain ⟨C2, hC2, h2⟩ := gammaFull_cPsiSq_sub_lintegral_le N hρ hρ' hκb0 hκb hθ hθκ' hq (κ := κ)
  obtain ⟨A, A', hA, hA', h3⟩ := gammaFull_cPsiCubeShift_sub_near_far.{u} N hρ hρ' hκb0 hκb hθ
    hθκ hq hB (κ := κ)
  obtain ⟨F, F', hF, hF', h4⟩ := gammaFull_cPsiCubeShift_sub_near_far.{u} N hρ hρ' hκb0 hκb hθ
    hθκ hq2 hB (κ := κ)
  obtain ⟨E1, E1', hE1, hE1', h5⟩ := gammaFull_cPsiCubeShift_near_far.{u} N hρ hκb0 hκb hq2 hB
    (κ := κ)
  obtain ⟨E2, E2', hE2, hE2', h6⟩ := gammaFull_cPsiCubeShift_near_far.{u} N hρ' hκb0 hκb hq2 hB
    (κ := κ)
  refine ⟨max (max C1 Cg) (max (max C2 (2 * max A A')) (max (max A A')
    (max (F * (E1 + E2)) (F' * (E1' + E2'))))), ?_, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left hC1)
  intro Ω _ P W ε ε' ξ ξ' C C' s s' hs hs' hW hε hε' hξ hξ' hC hC' hgr hgr' i j hi hj x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  have he : 0 < 1 / 2 - 3 * κ.1 + κbar := by linarith
  have hM0 : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hM : 0 ≤ (max ε ε') ^ θ + |s - s'| := add_nonneg hM0 (abs_nonneg _)
  have hle : (max ε ε') ^ θ ≤ (max ε ε') ^ θ + |s - s'| := le_add_of_nonneg_right (abs_nonneg _)
  have hU := measurable_gammaFullParam_cPsiCube_shift (κ := κ) hξ hC hgr x y
  have hU' := measurable_gammaFullParam_cPsiCube_shift (κ := κ) hξ' hC' hgr' x y
  refine gammaShift_entry_sub_lintegral_le hq hd0 hM (fun ω => gammaFullParam N κ C (ξ ω) y x)
    (fun ω => gammaFullParam N κ C' (ξ' ω) y x)
    (sgp_mono (h1 hW hε hε' hξ hξ' x y) hC1 (Real.rpow_nonneg hd0 _) hle)
    (fun k => sgp_mono (hg hW hε hε' hξ hξ' k x y) hCg (Real.rpow_nonneg hd0 _) hle)
    (sgp_mono (h2 hW hε hε' hξ hξ' hgr hgr' x y) hC2 (Real.rpow_nonneg hd0 _) hle) ?_ ?_ i j hi hj
  · obtain ⟨hn, hf⟩ := h3 hs hs' hW hε hε' hξ hξ' hC hC' hgr hgr' x y
    have := gammaFull_gap_of_near (P := P) (q := q) (M := (max ε ε') ^ θ + |s - s'|)
      (t := parabolicSemigroup.scaleDist y x) (d := parabolicSemigroup.scaleDist y x)
      (e := 1 / 2 - 3 * κ.1 + κbar) (f := fun ω => (gammaFullParam N κ C (ξ ω) y x).cPsiCube -
        (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube) hA hA' hM he.le le_rfl hd0 hn hf
    exact this
  · obtain ⟨hn, hf⟩ := h4 hs hs' hW hε hε' hξ hξ' hC hC' hgr hgr' x y
    obtain ⟨gn, gf⟩ := h5 hs hW hε hξ hC hgr x y
    obtain ⟨gn', gf'⟩ := h6 hs' hW hε' hξ' hC' hgr' x y
    have hsum : ∀ (hd1 : parabolicSemigroup.scaleDist y x ≤ 1), ∫⁻ ω,
        ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube + (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube‖ₑ ^
          (2 * q) ∂P ≤ ENNReal.ofReal ((E1 + E2) * parabolicSemigroup.scaleDist y x ^
            (1 / 2 - 3 * κ.1 + κbar)) ^ (2 * q) := fun hd1 => by
      have := lintegral_enorm_pow_add_le hq2 hU.aestronglyMeasurable hU'.aestronglyMeasurable
        (gn hd1) (gn' hd1) (mul_nonneg hE1 (Real.rpow_nonneg hd0 _))
        (mul_nonneg hE2 (Real.rpow_nonneg hd0 _))
      exact le_ofReal_pow_mono this (le_of_eq (by ring))
    have hfar : ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube +
        (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal (E1' + E2') ^ (2 * q) :=
      lintegral_enorm_pow_add_le hq2 hU.aestronglyMeasurable hU'.aestronglyMeasurable gf gf'
        hE1' hE2'
    have hprod := gammaFull_prod_gap (P := P) (q := q) (hU.sub hU').aemeasurable
      (hU.add hU').aemeasurable (A := F) (A' := F') (B := E1 + E2) (B' := E1' + E2')
      (M := (max ε ε') ^ θ + |s - s'|) (d := parabolicSemigroup.scaleDist y x)
      (e := 1 / 2 - 3 * κ.1 + κbar) (e' := 1 - 6 * κ.1 + κbar) hF hF' (add_nonneg hE1 hE2) hM
      hd0 he (by linarith) (by linarith) hn hf hsum hfar
    have e : ∀ ω, ((gammaFullParam N κ C (ξ ω) y x).cPsiCube -
        (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube) *
        ((gammaFullParam N κ C (ξ ω) y x).cPsiCube + (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube)
        = (gammaFullParam N κ C (ξ ω) y x).cPsiCube * (gammaFullParam N κ C (ξ ω) y x).cPsiCube -
          (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube *
            (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube := fun ω => by ring
    simpa only [Pi.sub_apply, Pi.add_apply, e] using hprod

end RegularityStructures.Phi43

end
