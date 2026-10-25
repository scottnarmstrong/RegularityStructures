/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionData

/-!
# Group identities for the explicit smooth renormalised extension

The character-recentring construction supplies actual group and covariance
identities on every retained symbol. These are necessary algebraic fields
of the eventual Model, not a substitute for proving agreement with the
source tensor formula on H0 [Hai14, (8.34), Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43.CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

/-- The corrected transition is the identity at equal base points. -/
theorem renormalisedExtensionGamma_self (c : RenormalisationConstants) (x : ParabolicSpace) :
    D.renormalisedExtensionGamma c x x = LinearMap.id := by
  unfold renormalisedExtensionGamma renormalisedExtensionGammaParameter
  rw [structureGroupInv_mul, structureGroupMap_zero]

/-- The corrected transitions satisfy the group composition identity. -/
theorem renormalisedExtensionGamma_comp (c : RenormalisationConstants)
    (x y z : ParabolicSpace) :
    (D.renormalisedExtensionGamma c x y).comp (D.renormalisedExtensionGamma c y z) =
      D.renormalisedExtensionGamma c x z := by
  unfold renormalisedExtensionGamma renormalisedExtensionGammaParameter
  rw [structureGroupMap_comp, structureGroupMul_assoc]
  rw [← structureGroupMul_assoc (D.renormalisedExtensionCharacter c y)
    (structureGroupInv (D.renormalisedExtensionCharacter c y))
    (D.renormalisedExtensionCharacter c z)]
  rw [structureGroupMul_right_inv, structureGroup_zero_mul]

/-- Full retained covariance of the explicitly defined function-valued lift.
Source-tensor agreement is not asserted by this group calculation. -/
theorem renormalisedExtensionPi_gamma (c : RenormalisationConstants)
    (x y : ParabolicSpace) (v : T) :
    D.renormalisedExtensionPi c x (D.renormalisedExtensionGamma c x y v) =
      D.renormalisedExtensionPi c y v := by
  change D.renormalisedExtensionGlobalPi c
      (structureGroupMap (D.renormalisedExtensionCharacter c x)
        (structureGroupMap (structureGroupInv (D.renormalisedExtensionCharacter c x) *
          D.renormalisedExtensionCharacter c y) v)) =
    D.renormalisedExtensionGlobalPi c
      (structureGroupMap (D.renormalisedExtensionCharacter c y) v)
  have hm : (structureGroupMap (D.renormalisedExtensionCharacter c x)).comp
      (structureGroupMap (structureGroupInv (D.renormalisedExtensionCharacter c x) *
        D.renormalisedExtensionCharacter c y)) =
      structureGroupMap (D.renormalisedExtensionCharacter c y) := by
    rw [structureGroupMap_comp, ← structureGroupMul_assoc,
      structureGroupMul_right_inv, structureGroup_zero_mul]
  exact congrArg (D.renormalisedExtensionGlobalPi c) (LinearMap.congr_fun hm v)

/-- Finite expansion into the actual global renormalised tree functions. -/
theorem renormalisedExtensionPi_eq_global_sum (c : RenormalisationConstants)
    (x y : ParabolicSpace) (v : T) :
    D.renormalisedExtensionPi c x v y =
      ∑ τ : Symbol,
        structureGroupMap (D.renormalisedExtensionCharacter c x) v τ *
          D.renormalisedExtensionGlobalBasis c τ y := by
  rw [renormalisedExtensionPi, LinearMap.comp_apply,
    renormalisedExtensionGlobalPi, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

end RegularityStructures.Phi43.CanonicalData

end
