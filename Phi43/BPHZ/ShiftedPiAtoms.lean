/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiCalculus
public import Phi43.BPHZ.BphzCauchyPiAll
public import Phi43.BPHZ.PositivePiMomentIPsiBound
import Mathlib.Tactic

/-!
# The atoms of the shifted moment bounds

`ShiftedPiAtoms N ρ κ κbar q C₁ C₂ Cᵢ C_g` bundles the unshifted bounds from which every shifted
row is built (Minkowski and Hölder): the single `Π`-bounds of all non-polynomial symbols below
`γ` at the exponents `q` and `2q`, the `iPsi` row (above `γ`), and the `L^(2q)` bound of the
gradients `shiftedPiGrad`.  `shiftedPiAtoms_exists` produces them from `BphzCauchyMoments`.
-/

@[expose] public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The unshifted inputs of the shifted moment bounds. -/
structure ShiftedPiAtoms (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (κ : Kappa) (κbar : ℝ) (q : ℕ)
    (C1 C2 Ci Cg : ℝ) : Prop where
  nonneg : 0 ≤ C1 ∧ 0 ≤ C2 ∧ 0 ≤ Ci ∧ 0 ≤ Cg
  single : ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
    PiSingleBound.{u} N ρ κ κbar q i C1
  double : ∀ i, i ∉ piDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
    PiSingleBound.{u} N ρ κ κbar (2 * q) i C2
  iPsi : PiSingleBound.{u} N ρ κ κbar q Symbol.iPsi Ci
  grad1 : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
    IsRegularisedNoise P W ρ ε ξ → ∀ (x : ParabolicSpace) (k : Fin 3),
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k) Cg
  grad : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
    IsRegularisedNoise P W ρ ε ξ → ∀ (x : ParabolicSpace) (k : Fin 3),
    ShiftMom P (2 * q) (fun ω => shiftedPiGrad N ξ ω x k) Cg

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ}

theorem shiftedPiAtoms_exists (hmiss : BphzCauchyMoments.{u} N κ) (hρ : IsMollifier ρ)
    (hκ0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) (hq : 1 ≤ q) :
    ∃ C1 C2 Ci Cg : ℝ, ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg := by
  obtain ⟨C1, hC1, h1⟩ := exists_piSingleBound_all hmiss hρ hκ0 hκb hq
  obtain ⟨C2, hC2, h2⟩ := exists_piSingleBound_all hmiss hρ hκ0 hκb (q := 2 * q) (by omega)
  obtain ⟨Ci, hCi, hi⟩ := regPi_iPsi_lintegral_enorm_pow_le.{u} N hρ κ hκ0 hκb hq
  obtain ⟨Cg, hCg, hg⟩ := gammaFull_grad_lintegral_le.{u} N hρ (q := 2 * q) (by omega)
  obtain ⟨Cg', hCg', hg'⟩ := gammaFull_grad_lintegral_le.{u} N hρ (q := q) hq
  refine ⟨C1, C2, Ci, Cg + Cg', ⟨⟨hC1, hC2, hCi, by positivity⟩, h1, h2, ?_, ?_, ?_⟩⟩
  · intro Ω _ P W ε ξ hW hε hξ hgr t ht x
    exact hi hW hε hξ (Filter.Eventually.of_forall hgr) t ht x
  · intro Ω _ P W ε ξ hW hε hξ x k
    exact lintegral_enorm_pow_mono (hg' hW hε hξ k (spaceTimeProj x)) (by linarith)
  · intro Ω _ P W ε ξ hW hε hξ x k
    exact lintegral_enorm_pow_mono (hg hW hε hξ k (spaceTimeProj x)) (by linarith)

end RegularityStructures.Phi43

end
