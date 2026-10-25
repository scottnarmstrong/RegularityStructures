/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.QuadraticIntegration
public import Phi43.Structure.RenormalisedExtensionAdmissible
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Polynomial.Model.Reg
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Heat.Annihilating.Translate

/-!
# Actual models realise the degree≤2 polynomial sector

The time monomial and spatial quadratic monomials have their actual
pointwise polynomial realisations. The integration clause is unchanged,
so this supplies the larger polynomial interface needed by the fixed point
[Hai14, Definition 5.9, Section 9.4, Proposition 9.8].
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem canonicalPi_polynomial_quadratic (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (x : ParabolicSpace) (k : PolyIndex 3) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis (phi43QuadraticPolyEmb k)) =
      polyEval x (Pi.single k 1) := by
  funext y
  rw [CanonicalData.canonicalPi_basis, polyEval_single]
  have hk := phi43QuadraticIndex_mem k
  simp only [phi43QuadraticIndices, Finset.mem_insert, Finset.mem_singleton] at hk
  change (hairerCanonicalData (κ := κ) N noise).localPiBasis x
    (phi43QuadraticSymbolOfIndex k.1) y = evalParabolic (MvPolynomial.monomial k.1 1) (y - x)
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals rw [hk]
  all_goals
    simp [phi43QuadraticSymbolOfIndex, Finsupp.single_apply,
      CanonicalData.localPiBasis, CanonicalData.localPolynomialQuadratic,
      CanonicalData.relCoord, evalParabolic, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype, Fin.prod_univ_succ, parabolicCoords_sub_apply]
  all_goals ring

theorem renormalisedExtensionPi_polynomial_quadratic (N : ℕ) {κ : Kappa}
    (noise : CanonicalNoise) (C : RenormalisationConstants) (x : ParabolicSpace) (k : PolyIndex 3) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
        (basis (phi43QuadraticPolyEmb k)) = polyEval x (Pi.single k 1) := by
  have hs : (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
      (basis (phi43QuadraticPolyEmb k)) =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis (phi43QuadraticPolyEmb k)) := by
    rw [renormalisedExtensionPi_basis_form, CanonicalData.canonicalPi_basis]
    rcases phi43QuadraticPolyEmb_cases k with h | h | ⟨i, h⟩ | ⟨p, h⟩ <;>
      rw [h] <;> rfl
  rw [hs, canonicalPi_polynomial_quadratic]

private theorem coord_symm_single (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

/-- Definition 5.9 with the full degree≤2 polynomial sector. -/
theorem canonicalRenormalisedModel_isRealising_quadratic (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).IsRealisingP (annKernel0C N)
      (gamma κ) (phi43PolynomialSectorQuadratic κ) phi43AbstractIntegration phi43IntegrationSector := by
  refine ⟨(canonicalRenormalisedModel_isRealising N κ noise Cg q hg C).realises, ?_⟩
  intro x k t z
  change (if 0 < t then parabolicSemigroup.apply t
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
      (phi43CoordinateEquiv.symm (Pi.single (phi43QuadraticPolyEmb k) 1))) z else 0) = _
  rw [coord_symm_single, renormalisedExtensionPi_polynomial_quadratic]
  rfl

end RegularityStructures.Phi43

end
