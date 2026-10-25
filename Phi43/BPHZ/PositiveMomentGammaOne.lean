/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaAlgebra
public import Phi43.Structure.AbstractPolynomial
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Polynomial.Model.Unit
public import RegularityStructures.Analysis.Kernel.Conservative

/-!
# The `1`-entries of `Γ` are differences of regularised `Π`

For a polynomial compatible model `Z` of `phi43RegularityStructure κ` the regularisation of
`Π_y 1` is the constant `1` (`regPi_single_one_of_isPolyCompatible`), and `Q_t Π_y Γ_{yx} = Q_t Π_x`
(`Model.regPi_gammaMap`).  Hence for `τ` with `Γ_{yx} e_τ = e_τ + c e_1` the entry `c` equals
`Q_t Π_x e_τ (z) - Q_t Π_y e_τ (z)` for every `t > 0` and `z`
(`gammaMap_one_entry_eq_sub`); this applies to `I(Ψ²)`, `I(Ψ³)` and `Xᵢ`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {κ : Kappa} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- Polynomial compatibility gives `Q_t Π_y 1 = 1`. -/
theorem regPi_single_one_of_isPolyCompatible
    (hpoly : Z.IsPolyCompatible (phi43PolynomialSector κ)) (y : ParabolicSpace) {t : ℝ}
    (ht : 0 < t) (z : ParabolicSpace) :
    Z.regPi y (Pi.single Symbol.one (1 : ℝ) : Symbol → ℝ) t z = 1 := by
  let k0 : PolyIndex 2 := ⟨0, by simp [weight_parabolicWeight]⟩
  have hk : (phi43PolynomialSector κ).emb k0 = Symbol.one :=
    (phi43PolynomialSector_emb κ ▸ phi43PolyEmb_eq_one (k := k0) rfl)
  have h := hpoly y k0 t z
  rw [hk] at h
  rw [h, polyReg_of_pos _ _ ht]
  have : polyEval y (Pi.single k0 1 : PolyIndex 2 → ℝ) = fun _ => 1 :=
    funext fun w => by rw [polyEval_single]; simp [k0, evalParabolic]
  rw [this]
  simp only [RegularisingSemigroup.apply, mul_one]
  exact parabolicSemigroup_isConservative ht z

/-- The `1`-entry of `Γ_{yx} e_τ` is the difference of the regularised `Π`'s at the two base
points, provided `Γ_{yx} e_τ = e_τ + c e_1`. -/
theorem gammaMap_one_entry_eq_sub
    (hpoly : Z.IsPolyCompatible (phi43PolynomialSector κ)) (y x : ParabolicSpace)
    (τ : Symbol)
    (h : Z.gammaMap y x (Pi.single τ (1 : ℝ) : Symbol → ℝ) = (Pi.single τ (1 : ℝ) : Symbol → ℝ) +
      Z.gammaMap y x (Pi.single τ (1 : ℝ) : Symbol → ℝ) Symbol.one •
        (Pi.single Symbol.one (1 : ℝ) : Symbol → ℝ))
    {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Z.gammaMap y x (Pi.single τ (1 : ℝ) : Symbol → ℝ) Symbol.one =
      Z.regPi x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t z -
        Z.regPi y (Pi.single τ (1 : ℝ) : Symbol → ℝ) t z := by
  have h1 := Z.regPi_gammaMap y x (Pi.single τ (1 : ℝ) : Symbol → ℝ) t z
  rw [h, Z.regPi_add, Z.regPi_smul, regPi_single_one_of_isPolyCompatible hpoly y ht z] at h1
  linarith

end RegularityStructures.Phi43

end
