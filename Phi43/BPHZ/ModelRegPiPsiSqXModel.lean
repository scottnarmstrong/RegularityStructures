/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXPeriodise
public import Phi43.BPHZ.ModelRegPiTree
public import Phi43.BPHZ.ModelRegPiRandom
public import RegularityStructures.Abstract.Model

/-!
# The realisation `Z.regPi` of `Ψ² Xᵢ` is the Wick square tested against `g_i`

For a model `Z` with `IsPhi43ModelOf N κ (ξ ω) C Z` the realisation of `Ψ² Xᵢ` is, by
`hairerCanonicalData_renormalisedPi_basis_psiSqX_eq`, the `ℝ⁴` integral

`Z.regPi x (Pi.single (Ψ²Xᵢ) 1) t x = ∫ Q_t(x, y) :Ψ²:(proj y) (yᵢ - xᵢ) dy`

(`IsPhi43ModelOf.regPi_psiSqX_eq_integral_kernel`), where the displacement `yᵢ - xᵢ` is the `ℝ⁴`
coordinate difference, not a function of `proj y`.  Almost surely (given integrability) this is
`∫_{ℝ × T³} g_i(u) :Ψ²:(u) du` with the coordinate-weighted periodised kernel
`g_i = semigroupPeriodisedX t x i` (`ae_regPi_single_psiSqX_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} {N : ℕ} {κ : Kappa} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- **`regPi` on `Ψ² Xᵢ` as an `ℝ⁴` integral.** -/
theorem Statements.IsPhi43ModelOf.regPi_psiSqX_eq_integral_kernel (hZ : Statements.IsPhi43ModelOf N κ (ξ ω) C Z)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    Z.regPi x (Pi.single (Symbol.psiSqX i) 1) t x =
      ∫ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
        (hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) * (y.2 i - x.2 i)) := by
  have hf := hZ.isSmoothOnSpaceTime
  obtain ⟨noise, hn, -, h2, -⟩ := hZ
  rw [h2 (Symbol.psiSqX i) (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht x]
  have hb := CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiSqX_eq
    (κ := κ) (N := N) (ξ := ξ) (ω := ω) (noise := noise) x C hn hf i
  simp only [RegularisingSemigroup.apply]
  rw [hb]

variable [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}

/-- **Random corollary for `Ψ² Xᵢ`.** -/
theorem ae_regPi_single_psiSqX_eq
    {Zs : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hZ : ∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
      ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants) (Zs ω))
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (hint : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y *
        (hairerPsiWickSquare N ρ ε ξ ω (spaceTimeProj y) * (y.2 i - x.2 i)))) :
    (fun ω => (Zs ω).regPi x (Pi.single (Symbol.psiSqX i) 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodisedX t x i u * hairerPsiWickSquare N ρ ε ξ ω u := by
  filter_upwards [hZ, hint] with ω hω hi
  rw [hω.regPi_psiSqX_eq_integral_kernel i ht x]
  exact (integral_semigroup_kernel_coord_mul_comp_proj t x i
    (measurable_slice_of_uncurry (measurable_hairerPsiWickSquare_uncurry N hξ) ω) hi).2

end RegularityStructures.Phi43

end
