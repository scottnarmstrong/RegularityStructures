/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentField

/-!
# The fields of the positive products `I(Ψ)Ψ` and `I(Ψ)(Ψ² - c₁)`

For the canonical model of a smooth noise `ξ ω`, `Π_x I(Ψ)Ψ (y) = v₁(x, y) Ψ(y)` and
`Π_x I(Ψ)Ψ² (y) = v₁(x, y) (Ψ(y)² - C₁)`, where `v₁(x, y) = hairerIPsiRecentred N ξ ω x y` is the
recentred `I(Ψ)` with its spatial gradient [Hai14, (8.4), Prop. 8.27].  This module names the two
fields on `ℝ⁴ × ℝ⁴` (`hairerIPsiPsiField`, `hairerIPsiPsiSqField`) and records that
`Q_t Π_x τ (x) = ∫ Q_t(x, y) F_x(y) dy` for them (`regPi_iPsiPsi_eq_integral_field`,
`regPi_iPsiPsiSq_eq_integral_field`).  It is the common interface of the covariance layer
(second moments) and of the chaos layer (all moments) of the moment bounds for the product symbols.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The field `y ↦ Π_x I(Ψ)Ψ (y) = v₁(x, y) Ψ(y)` on `ℝ⁴`. -/
def hairerIPsiPsiField {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (x : ParabolicSpace) (ω : Ω)
    (y : ParabolicSpace) : ℝ :=
  hairerIPsiRecentred N ξ ω x y * hairerPsiField N ξ ω (spaceTimeProj y)

/-- The field `y ↦ Π_x I(Ψ)Ψ² (y) = v₁(x, y) (Ψ(y)² - c₁)` on `ℝ⁴`. -/
def hairerIPsiPsiSqField {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ : ℝ)
    (x : ParabolicSpace) (ω : Ω) (y : ParabolicSpace) : ℝ :=
  hairerIPsiRecentred N ξ ω x y * hairerTreePsiSq N ξ c₁ ω (spaceTimeProj y)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ}
  {ω : Ω}

/-- `Q_t Π_x I(Ψ)Ψ (x) = ∫ Q_t(x, y) v₁(x, y) Ψ(y) dy` for the canonical model. -/
theorem regPi_iPsiPsi_eq_integral_field (hf : IsSmoothOnSpaceTime (ξ ω))
    (hg : Statements.HasPhi43NoiseGrowth (ξ ω)) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ C (ξ ω)).regPi x (Pi.single Symbol.iPsiPsi (1 : ℝ) : Symbol → ℝ)
        t x =
      ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y := by
  rw [regPi_canonicalModelOfLift_eq_integral hf hg _ ht x, extensionPi_iPsiPsi_eq hf x]
  rfl

/-- `Q_t Π_x I(Ψ)Ψ² (x) = ∫ Q_t(x, y) v₁(x, y) (Ψ(y)² - C₁) dy` for the canonical model. -/
theorem regPi_iPsiPsiSq_eq_integral_field (hf : IsSmoothOnSpaceTime (ξ ω))
    (hg : Statements.HasPhi43NoiseGrowth (ξ ω)) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ C (ξ ω)).regPi x
        (Pi.single Symbol.iPsiPsiSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ (C₁ C) x ω y := by
  rw [regPi_canonicalModelOfLift_eq_integral hf hg _ ht x, extensionPi_iPsiPsiSq_eq hf x]
  rfl

end RegularityStructures.Phi43

end
