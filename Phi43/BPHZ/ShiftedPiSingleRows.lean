/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSingleBase
import Mathlib.Tactic

/-!
# Single shifted bounds: the rows independent of the constants and the first shifted rows

The rows `Ξ, Ψ, ΨXᵢ, I(Ψ²), I(Ψ)Ψ, I(Ψ²)Ψ` do not depend on the constants, and the shifted rows
`Ψ², Ψ³, Ψ²Xᵢ, I(Ψ)Ψ², I(Ψ²)Ψ²` are the unshifted rows plus `-a` times a row of higher degree
(or the deterministic `-a ∫ Q_t`, `-a ∫ Q_t (yₖ - xₖ)`, `-b ∫ Q_t`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar : ℝ} {q : ℕ} {C1 C2 Ci Cg : ℝ}

theorem shiftedPi_shift_noise {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    {C C' : RenormalisationConstants} (x : ParabolicSpace) (hf : IsSmoothOnSpaceTime (ξ ω))
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .noise) y =
      (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .noise) y := by
  rw [shiftedPi_row_treeField C' x hf (τ := .noise) (by simp [isFMinus]) (fun i h => by cases h),
    shiftedPi_row_treeField C x hf (τ := .noise) (by simp [isFMinus]) (fun i h => by cases h)]
  rfl

/-- A row independent of the constants has the same bound for every shift. -/
theorem shiftedPi_single_of_indep (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) {τ : Symbol}
    (h1 : τ ≠ .one) (hx : ∀ j, τ ≠ .x j) (hlt : homogeneity κ τ < gamma κ)
    (hshift : ∀ {Ω : Type u} {ξ : Ω → SpaceTime → ℝ} {ω : Ω} (hf : IsSmoothOnSpaceTime (ξ ω))
      (C C' : RenormalisationConstants) (x y : ParabolicSpace),
      (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
          C' x (basis τ) y =
        (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
          C x (basis τ) y) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q τ B C1 := by
  refine PiShiftSingleBound.of_shiftMom ?_
  intro Ω _ P W ε ξ c hc hW hε hξ hgr t ht x
  refine ShiftMom.congr (fun ω => ?_) (A.mom h1 hx hlt hW hε hξ hgr ht x)
  exact shiftedPi_reg_congr x (hξ.1 ω) (hgr ω) ht.1 (fun y => hshift (hξ.1 ω) _ _ x y)

theorem shiftedPi_single_noise (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q .noise B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_noise x hf y) B

theorem shiftedPi_single_psi (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q .psi B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_psi x hf y) B

theorem shiftedPi_single_psiX (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (k : Fin 3)
    (B : ℝ) : PiShiftSingleBound.{u} N ρ κ κbar q (.psiX k) B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_psiX x hf k y) B

theorem shiftedPi_single_iPsiSq (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiSq B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiSq x hf y) B

theorem shiftedPi_single_iPsiPsi (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiPsi B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiPsi x hf y) B

theorem shiftedPi_single_iPsiSqPsi (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (B : ℝ) :
    PiShiftSingleBound.{u} N ρ κ κbar q .iPsiSqPsi B C1 :=
  shiftedPi_single_of_indep A (by simp) (by simp) (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiSqPsi x hf y) B

end RegularityStructures.Phi43

end
