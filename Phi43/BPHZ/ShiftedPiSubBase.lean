/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubAtoms
public import Phi43.BPHZ.ShiftedPiSingleAll
import Mathlib.Tactic

/-!
# Accessors for the shifted difference bounds

The reduction of `PiShiftSubBound` to `ShiftMom` statements, and the unshifted difference atoms in
the form `S * D * T` with `D = (max ε ε')^θ + ‖c - c'‖` and `T = t^((homogeneity κ σ + κbar)/4)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

/-- `PiShiftSubBound` from the `ShiftMom` form. -/
theorem PiShiftSubBound.of_shiftMom {τ : Symbol} {B C : ℝ}
    (h : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
      {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (c c' : RenormalisationConstants),
      ‖c‖ ≤ B → ‖c'‖ ≤ B → IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
      ε' ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      ShiftMom P q (fun ω => shiftedPiReg N κ (shiftConst N ρ ε c) (ξ ω) x t τ -
          shiftedPiReg N κ (shiftConst N ρ' ε' c') (ξ' ω) x t τ)
        (C * ((max ε ε') ^ θ + ‖c - c'‖) * t ^ ((homogeneity κ τ + κbar) / 4))) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q τ B C :=
  fun c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x =>
    h c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x

theorem ShiftMom.toD {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q : ℕ}
    {S m T D : ℝ} (h : ShiftMom P q f (S * m * T)) (hS : 0 ≤ S) (hT : 0 ≤ T) (hm : m ≤ D) :
    ShiftMom P q f (S * D * T) :=
  h.mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hS) hT)

theorem ShiftMom.toD' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q : ℕ}
    {S m D : ℝ} (h : ShiftMom P q f (S * m)) (hS : 0 ≤ S) (hm : m ≤ D) :
    ShiftMom P q f (S * D) :=
  h.mono (mul_le_mul_of_nonneg_left hm hS)

theorem abs_fst_sub_le_norm (c c' : RenormalisationConstants) : |c.1 - c'.1| ≤ ‖c - c'‖ := by
  have := norm_fst_le (c - c')
  rwa [Real.norm_eq_abs] at this

theorem abs_snd_sub_le_norm (c c' : RenormalisationConstants) : |c.2 - c'.2| ≤ ‖c - c'‖ := by
  have := norm_snd_le (c - c')
  rwa [Real.norm_eq_abs] at this

/-- The difference atom of exponent `q` in `ShiftMom` form, with the factor `D`. -/
theorem ShiftedPiSubAtoms.momSub
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) :
    ShiftMom P q (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ)
      (S1 * D * t ^ ((homogeneity κ σ + κbar) / 4)) :=
  ShiftMom.toD (SA.sub1 σ (shiftedPi_not_mem_piDeterministic h1 hx) (homogeneity_deg_lt_gamma hlt)
    hW hε hε' hξ hξ' hgr hgr' t ht x) SA.nonneg.1 (Real.rpow_nonneg ht.1.le _) hD

/-- The difference atom of exponent `2q`. -/
theorem ShiftedPiSubAtoms.momSub2
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) :
    ShiftMom P (2 * q) (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ)
      (S2 * D * t ^ ((homogeneity κ σ + κbar) / 4)) :=
  ShiftMom.toD (SA.sub2 σ (shiftedPi_not_mem_piDeterministic h1 hx) (homogeneity_deg_lt_gamma hlt)
    hW hε hε' hξ hξ' hgr hgr' t ht x) SA.nonneg.2.1 (Real.rpow_nonneg ht.1.le _) hD

/-- The `iPsi` difference atom. -/
theorem ShiftedPiSubAtoms.momSubIPsi
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) :
    ShiftMom P q (fun ω => shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t .iPsi -
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t .iPsi)
      (Si * D * t ^ ((homogeneity κ .iPsi + κbar) / 4)) :=
  ShiftMom.toD (SA.iPsi hW hε hε' hξ hξ' hgr hgr' t ht x) SA.nonneg.2.2.1
    (Real.rpow_nonneg ht.1.le _) hD

/-- The gradient difference atoms with the factor `D`. -/
theorem ShiftedPiSubAtoms.momGrad
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (x : ParabolicSpace) (k : Fin 3) (D : ℝ) (hD : (max ε ε') ^ θ ≤ D) :
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k) (Sg * D) :=
  ShiftMom.toD' (SA.grad1 hW hε hε' hξ hξ' x k) SA.nonneg.2.2.2 hD

theorem ShiftedPiSubAtoms.momGrad2
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (x : ParabolicSpace) (k : Fin 3) (D : ℝ) (hD : (max ε ε') ^ θ ≤ D) :
    ShiftMom P (2 * q) (fun ω => shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k) (Sg * D) :=
  ShiftMom.toD' (SA.grad2 hW hε hε' hξ hξ' x k) SA.nonneg.2.2.2 hD

end RegularityStructures.Phi43

end
