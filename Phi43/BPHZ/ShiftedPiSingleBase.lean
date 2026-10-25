/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiAtoms
public import Phi43.BPHZ.ShiftedMomentDefs
import Mathlib.Tactic

/-!
# Accessors for the single shifted bounds

Reductions of `PiShiftSingleBound` to `ShiftMom` statements for the random variables
`ω ↦ Q_t Π^{C}_x τ (x)`, and the accessors extracting the atoms of `ShiftedPiAtoms` in the
`ShiftMom` form with the exponent `(homogeneity κ σ + κbar) / 4`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ} {C1 C2 Ci Cg : ℝ}

/-- `PiShiftSingleBound` from the `ShiftMom` form. -/
theorem PiShiftSingleBound.of_shiftMom {τ : Symbol} {B C : ℝ}
    (h : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
      {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} (c : RenormalisationConstants), ‖c‖ ≤ B →
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ShiftMom P q (fun ω => shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t τ)
        (C * t ^ ((homogeneity κ τ + κbar) / 4))) :
    PiShiftSingleBound.{u} N ρ κ κbar q τ B C :=
  fun c hc hW hε hξ hgr t ht x => h c hc hW hε hξ hgr t ht x

theorem shiftedPi_not_mem_piDeterministic {σ : Symbol} (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) :
    σ ∉ piDeterministic := by
  rintro ⟨k, hk⟩
  unfold phi43PolyEmb at hk
  split_ifs at hk
  · exact h1 hk.symm
  · exact hx 0 hk.symm
  · exact hx 1 hk.symm
  · exact hx 2 hk.symm

theorem homogeneity_deg_lt_gamma {σ : Symbol} (h : homogeneity κ σ < gamma κ) :
    (phi43RegularityStructure κ).deg σ < gamma κ := by
  rw [phi43RegularityStructure_deg]
  exact h

/-- The atom of exponent `q` in `ShiftMom` form. -/
theorem ShiftedPiAtoms.mom (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) :
    ShiftMom P q (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ)
      (C1 * t ^ ((homogeneity κ σ + κbar) / 4)) :=
  A.single σ (shiftedPi_not_mem_piDeterministic h1 hx) (homogeneity_deg_lt_gamma hlt) hW hε hξ
    hgr t ht x

/-- The atom of exponent `2q` in `ShiftMom` form. -/
theorem ShiftedPiAtoms.mom2 (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) :
    ShiftMom P (2 * q) (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ)
      (C2 * t ^ ((homogeneity κ σ + κbar) / 4)) :=
  A.double σ (shiftedPi_not_mem_piDeterministic h1 hx) (homogeneity_deg_lt_gamma hlt) hW hε hξ
    hgr t ht x

/-- The `iPsi` atom in `ShiftMom` form. -/
theorem ShiftedPiAtoms.momIPsi (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) :
    ShiftMom P q (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsi)
      (Ci * t ^ ((homogeneity κ .iPsi + κbar) / 4)) :=
  A.iPsi hW hε hξ hgr t ht x

end RegularityStructures.Phi43

end
