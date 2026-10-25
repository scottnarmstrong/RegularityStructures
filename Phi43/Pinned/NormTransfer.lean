/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Pinned.GammaPinned
public import Phi43.Structure.CanonicalModelExistence
import Mathlib.Tactic
public import RegularityStructures.Abstract.Model

/-!
# Norm transfer between renormalised canonical models

For two models `Z`, `Z'` with `Statements.IsRenormalisedCanonicalModel N κ noise C`, for instance a
model `Z` and the canonical model `canonicalRenormalisedModel N κ noise Cg q hg C` (which satisfies
the predicate by `canonicalRenormalisedModel_isRenormalisedCanonicalModel`):

* the `Γ`-bounds at the cutoff `gamma κ` coincide on every set
  (`gammaBoundOn_iff_of_isRenormalisedCanonicalModel`), because `Γ e_τ` agrees for `τ ≠ X₀` and
  `X₀` has degree `2 > γ`;
* the diagonal `Π`-bounds on pinned symbols coincide (`abs_regPi_diag_eq_of_pinned`).
-/

public section

open scoped NNReal ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {C : RenormalisationConstants}
  {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}

theorem homogeneity_lt_gamma_ne_x0 {τ : Symbol} (h : homogeneity κ τ < gamma κ) : τ ≠ .x0 := by
  have hk' : κ.1 < 1 / 16 := κ.2.2
  rintro rfl
  simp only [homogeneity, gamma] at h
  linarith

/-- The `Γ`-bound predicates of two renormalised canonical models coincide. -/
theorem gammaBoundOn_iff_of_isRenormalisedCanonicalModel
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') (c : ℝ) (S : Set ParabolicSpace) :
    Z.GammaBoundOn (gamma κ) c S ↔ Z'.GammaBoundOn (gamma κ) c S := by
  have key : ∀ i j x y, homogeneity κ i < gamma κ →
      Z.gammaMap y x (Pi.single i 1) j = Z'.gammaMap y x (Pi.single i 1) j := fun i j x y hi => by
    rw [gammaMap_single_eq_of_isRenormalisedCanonicalModel hZ hZ' (homogeneity_lt_gamma_ne_x0 hi)]
  unfold Model.GammaBoundOn
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun hi =>
    forall_congr' fun hj => forall_congr' fun x => forall_congr' fun hx =>
    forall_congr' fun y => forall_congr' fun hy => ?_
  rw [key i j x y hi]

/-- The diagonal `Π`-bound on pinned symbols transfers between renormalised canonical models. -/
theorem abs_regPi_diag_eq_of_pinned
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {τ : Symbol}
    (hτ : IsPinnedSymbol τ) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) :
    |Z.regPi x (Pi.single τ 1) t x| = |Z'.regPi x (Pi.single τ 1) t x| := by
  rw [regPi_eq_of_isRenormalisedCanonicalModel hZ hZ' hτ x ht x]

end RegularityStructures.Phi43

end
