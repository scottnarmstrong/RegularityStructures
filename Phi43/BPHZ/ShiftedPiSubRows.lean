/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubBase
import Mathlib.Tactic

/-!
# Shifted difference bounds: the rows independent of the constants and the first shifted rows

The difference of two shifted rows is the unshifted difference plus
`(c - c') R + c' (R - R')` for the rows `R` of higher degree (and the deterministic kernel mass and
first moment), which gives the factor `(max ε ε')^θ + ‖c - c'‖`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

/-- A row independent of the constants has the same difference bound for every shift. -/
theorem shiftedPi_sub_of_indep
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) {τ : Symbol}
    (h1 : τ ≠ .one) (hx : ∀ j, τ ≠ .x j) (hlt : homogeneity κ τ < gamma κ)
    (hshift : ∀ {Ω : Type u} {ξ : Ω → SpaceTime → ℝ} {ω : Ω} (hf : IsSmoothOnSpaceTime (ξ ω))
      (C C' : RenormalisationConstants) (x y : ParabolicSpace),
      (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
          C' x (basis τ) y =
        (hairerCanonicalData (κ := κ) (N := N) (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
          C x (basis τ) y) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q τ B S1 := by
  refine PiShiftSubBound.of_shiftMom ?_
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr' t ht x
  have hmx : (max ε ε') ^ θ ≤ (max ε ε') ^ θ + ‖c - c'‖ := le_add_of_nonneg_right (norm_nonneg _)
  refine ShiftMom.congr (fun ω => ?_) (SA.momSub h1 hx hlt hW hε hε' hξ hξ' hgr hgr' ht x _ hmx)
  rw [shiftedPi_reg_congr x (hξ.1 ω) (hgr ω) ht.1 (fun y => hshift (hξ.1 ω) _ _ x y),
    shiftedPi_reg_congr x (hξ'.1 ω) (hgr' ω) ht.1 (fun y => hshift (hξ'.1 ω) _ _ x y)]

theorem shiftedPi_sub_noise
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .noise B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_noise x hf y) B

theorem shiftedPi_sub_psi
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .psi B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_psi x hf y) B

theorem shiftedPi_sub_psiX
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (k : Fin 3) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q (.psiX k) B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_psiX x hf k y) B

theorem shiftedPi_sub_iPsiSq
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiSq B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiSq x hf y) B

theorem shiftedPi_sub_iPsiPsi
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiPsi B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiPsi x hf y) B

theorem shiftedPi_sub_iPsiSqPsi
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (B : ℝ) :
    PiShiftSubBound.{u} N ρ ρ' κ κbar θ q .iPsiSqPsi B S1 :=
  shiftedPi_sub_of_indep SA (by simp) (by simp)
    (by simp only [homogeneity, gamma]; linarith [κ.2.1])
    (fun hf _ _ x y => shiftedPi_shift_iPsiSqPsi x hf y) B

end RegularityStructures.Phi43

end
