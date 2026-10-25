/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeRealises
public import Phi43Statements.Defs.IsPhi43ModelOf
public import Phi43.BPHZ.SemigroupTestPeriodise
public import RegularityStructures.Abstract.Model

/-!
# The realisation `Z.regPi` of a Phi43 model on `F₋` is a tested tree field

For a model `Z` with `IsPhi43ModelOf N κ f C Z` and a tree `τ ∈ F₋` other than `Ψ²Xᵢ`,
the regularised realisation `Z.regPi x (Pi.single τ 1) t x` is the semigroup average

`∫_{ℝ⁴} Q_t(x, y) F_τ(proj x, proj y) dy`

of the pathwise tree field `F_τ = hairerTreeField` of the (smooth) noise `f`
(`regPi_single_eq_integral_kernel`), and, when the integrand is integrable, the integral against
the periodised kernel on `ℝ × T³` (`regPi_single_eq_integral_semigroupPeriodised`).

The statements are for a family `ξ : Ω → SpaceTime → ℝ` and a sample `ω` with
`IsPhi43ModelOf N κ (ξ ω) C Z`; the `ω`-free form is `Ω = Unit`, `ξ = fun _ => f`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} {N : ℕ} {κ : Kappa} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- A model of the periodic lift of `f` forces `f` to be smooth on space-time. -/
theorem Statements.IsPhi43ModelOf.isSmoothOnSpaceTime {f : SpaceTime → ℝ}
    (hZ : Statements.IsPhi43ModelOf N κ f C Z) : IsSmoothOnSpaceTime f := by
  obtain ⟨noise, hn, -⟩ := hZ
  have h : (fun p : ℝ × (Fin 3 → ℝ) => f (p.1, torusProj p.2)) = noise.zeta :=
    funext fun z => (hn z).symm
  unfold IsSmoothOnSpaceTime
  rw [h]
  exact noise.smooth

/-- **`regPi` on `F₋` is the semigroup average of the tree field.**  For `τ ∈ F₋` other than
`Ψ²Xᵢ`, `t > 0` and `x`, `Z.regPi x (Pi.single τ 1) t x` is `∫ Q_t(x, y) F_τ(proj x, proj y) dy`
over `ℝ⁴`.  No integrability hypothesis is needed: both sides are Bochner integrals of the same
function. -/
theorem Statements.IsPhi43ModelOf.regPi_single_eq_integral_kernel (hZ : Statements.IsPhi43ModelOf N κ (ξ ω) C Z)
    {τ : Symbol} (hτ : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    Z.regPi x (Pi.single τ 1) t x =
      ∫ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
        hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ (spaceTimeProj y) := by
  have hf := hZ.isSmoothOnSpaceTime
  obtain ⟨noise, hn, -, h2, -⟩ := hZ
  rw [h2 τ hτ x t ht x]
  have hb := CanonicalData.hairerCanonicalData_renormalisedPi_basis_eq_treeField (κ := κ) (N := N)
    (ξ := ξ) (ω := ω) (noise := noise) C x hn hf hτ hX
  simp only [RegularisingSemigroup.apply]
  rw [hb]

/-- **`regPi` on `F₋` against the periodised kernel.**  If the kernel times the lifted tree field
is integrable on `ℝ⁴`, then
`Z.regPi x (Pi.single τ 1) t x = ∫_{ℝ × T³} q^♯_t(x, u) F_τ(proj x, u) du`. -/
theorem Statements.IsPhi43ModelOf.regPi_single_eq_integral_semigroupPeriodised
    (hZ : Statements.IsPhi43ModelOf N κ (ξ ω) C Z)
    {τ : Symbol} (hτ : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace)
    (hG : Measurable (hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ))
    (hint : Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y *
      hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ (spaceTimeProj y))) :
    Z.regPi x (Pi.single τ 1) t x =
      ∫ u : SpaceTime, semigroupPeriodised t x u *
        hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ u := by
  rw [hZ.regPi_single_eq_integral_kernel hτ hX ht x]
  exact (integral_semigroup_kernel_mul_comp_proj t x hG hint).2

end RegularityStructures.Phi43

end
