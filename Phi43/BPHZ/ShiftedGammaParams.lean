/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaCube
public import Phi43.BPHZ.ShiftedGammaEntry
import Mathlib.Tactic

/-!
# Entry moments of the shifted `Γ`-parameter, single model

For `C` with `C₁ C = hairerWickConstant N ρ ε + s`, `|s| ≤ B`: the parameters `cPsi`, `cPsiGrad`,
`cPsiSq` do not depend on `C` (unshifted bounds), `cPsiCube` has the near/far bounds of
`gammaFull_cPsiCubeShift_near_far`, and `cPsiCube²` follows by `gammaFull_sq_gap`.  Feeding
these into `gammaShift_entry_lintegral_le` gives the moment of every random entry
(`gammaFull_entryShift_lintegral_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The shifted `cPsiCube` is a measurable function of the sample point. -/
theorem measurable_gammaFullParam_cPsiCube_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε s : ℝ} {N : ℕ} {κ : Kappa}
    {ξ : Ω → SpaceTime → ℝ} {C : RenormalisationConstants}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hC : C₁ C = hairerWickConstant N ρ ε + s)
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (x y : ParabolicSpace) :
    Measurable fun ω => (gammaFullParam N κ C (ξ ω) y x).cPsiCube := by
  have e : ∀ ω, (gammaFullParam N κ C (ξ ω) y x).cPsiCube =
      gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω +
        3 * s * (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) :=
    fun ω => gammaFullParam_cPsiCube_shift hC (hξ.1 ω) (hgr ω) y x
  simp_rw [e]
  refine (measurable_gammaWickCube_omega N hξ _ _).add (Measurable.const_mul ?_ _)
  refine Measurable.sub ?_ ?_ <;>
  exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id))

/-- **Moments of the random `Γ`-entries of the model with shifted constants.** -/
theorem gammaFull_entryShift_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {C : RenormalisationConstants} {s : ℝ}, |s| ≤ B →
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ C = hairerWickConstant N ρ ε + s → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ i j : Symbol, IsGammaFullRandom i → j ≠ i → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖structureGroupMap (gammaFullParam N κ C (ξ ω) y x) (basis i) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ i - homogeneity κ j + κbar)) ^ q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  have hq2 : 1 ≤ 2 * q := by omega
  obtain ⟨C1, hC1, h1⟩ := gammaFull_cPsi_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  obtain ⟨Cg, hCg, hg⟩ := gammaFull_cPsiGrad_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  obtain ⟨C2, hC2, h2⟩ := gammaFull_cPsiSq_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  obtain ⟨A, A', hA, hA', h3⟩ := gammaFull_cPsiCubeShift_near_far.{u} N hρ hκb0 hκb hq hB
    (κ := κ)
  obtain ⟨E, E', hE, hE', h4⟩ := gammaFull_cPsiCubeShift_near_far.{u} N hρ hκb0 hκb hq2 hB
    (κ := κ)
  refine ⟨max (max C1 Cg) (max (max C2 (2 * max A A')) (max (max A A')
    (max (E * E) (E' * E')))), ?_, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left hC1)
  intro Ω _ P W ε ξ C s hs hW hε hξ hC hgr i j hi hj x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  have he : 0 < 1 / 2 - 3 * κ.1 + κbar := by linarith
  refine gammaShift_entry_lintegral_le hq hd0 (fun ω => gammaFullParam N κ C (ξ ω) y x)
    (h1 hW hε hξ x y) (fun k => hg hW hε hξ k x y) (h2 hW hε hξ hgr x y) ?_ ?_ i j hi hj
  · obtain ⟨hn, hf⟩ := h3 hs hW hε hξ hC hgr x y
    have := gammaFull_gap_of_near (P := P) (q := q) (M := 1) (t := parabolicSemigroup.scaleDist y x)
      (d := parabolicSemigroup.scaleDist y x) (e := 1 / 2 - 3 * κ.1 + κbar)
      (f := fun ω => (gammaFullParam N κ C (ξ ω) y x).cPsiCube) hA hA' zero_le_one he.le le_rfl hd0
      (by simpa using hn) (by simpa using hf)
    simpa using this
  · obtain ⟨hn, hf⟩ := h4 hs hW hε hξ hC hgr x y
    exact gammaFull_sq_gap (P := P) (q := q) (f := fun ω => (gammaFullParam N κ C (ξ ω) y x).cPsiCube)
      hE hE' hd0 he (by linarith) (by linarith) hn hf

end RegularityStructures.Phi43

end
