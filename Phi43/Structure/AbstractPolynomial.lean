/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Abstract
public import RegularityStructures.Abstract.Integration
import Mathlib.Tactic.FinCases
import Mathlib.Tactic

/-!
# The polynomial sector of the finite Φ⁴₃ structure

For `N = 2`, the abstract polynomial basis consists of `1` and the three
spatial coordinates.  The parabolic time coordinate has degree two and is
therefore outside this strict polynomial cutoff, while it remains in the
concrete finite symbol set for products and Taylor bookkeeping.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The four polynomial basis symbols below parabolic degree two. -/
def phi43PolyEmb (k : PolyIndex 2) : Symbol :=
  if k.1 = 0 then .one
  else if k.1 (1 : Fin 4) = 1 then .x 0
  else if k.1 (2 : Fin 4) = 1 then .x 1
  else .x 2

private def phi43PolyZero : PolyIndex 2 :=
  ⟨0, by simp [weight_parabolicWeight]⟩

private theorem phi43PolyEmb_zero : phi43PolyEmb phi43PolyZero = .one := by
  simp [phi43PolyZero, phi43PolyEmb]

theorem polyIndex_two_cases (k : PolyIndex 2) :
    k.1 = 0 ∨ k.1 = Finsupp.single (1 : Fin 4) 1 ∨
      k.1 = Finsupp.single (2 : Fin 4) 1 ∨
      k.1 = Finsupp.single (3 : Fin 4) 1 := by
  have hk := k.2
  rw [weight_parabolicWeight] at hk
  have h0 : k.1 0 = 0 := by omega
  have hsum : k.1 1 + k.1 2 + k.1 3 ≤ 1 := by omega
  by_cases h1 : k.1 1 = 1
  · have h2 : k.1 2 = 0 := by omega
    have h3 : k.1 3 = 0 := by omega
    right
    left
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3]
  by_cases h2 : k.1 2 = 1
  · have h1' : k.1 1 = 0 := by omega
    have h3 : k.1 3 = 0 := by omega
    right
    right
    left
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [h0, h1', h2, h3]
  by_cases h3 : k.1 3 = 1
  · have h1' : k.1 1 = 0 := by omega
    have h2' : k.1 2 = 0 := by omega
    right
    right
    right
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [h0, h1', h2', h3]
  left
  have h1' : k.1 1 = 0 := by omega
  have h2' : k.1 2 = 0 := by omega
  have h3' : k.1 3 = 0 := by omega
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp [h0, h1', h2', h3']

theorem phi43PolyEmb_eq_one {k : PolyIndex 2} (hk : k.1 = 0) :
    phi43PolyEmb k = .one := by
  simp [phi43PolyEmb, hk]

theorem phi43PolyEmb_eq_x0 {k : PolyIndex 2}
    (hk : k.1 = Finsupp.single (1 : Fin 4) 1) :
    phi43PolyEmb k = .x 0 := by
  simp [phi43PolyEmb, hk]

theorem phi43PolyEmb_eq_x1 {k : PolyIndex 2}
    (hk : k.1 = Finsupp.single (2 : Fin 4) 1) :
    phi43PolyEmb k = .x 1 := by
  simp [phi43PolyEmb, hk]

theorem phi43PolyEmb_eq_x2 {k : PolyIndex 2}
    (hk : k.1 = Finsupp.single (3 : Fin 4) 1) :
    phi43PolyEmb k = .x 2 := by
  simp [phi43PolyEmb, hk]

theorem phi43PolyEmb_injective : Function.Injective phi43PolyEmb := by
  intro k l hkl
  rcases polyIndex_two_cases k with hk | hk | hk | hk <;>
    rcases polyIndex_two_cases l with hl | hl | hl | hl
  all_goals simp [phi43PolyEmb, hk, hl] at hkl
  all_goals exact Subtype.ext (hk.trans hl.symm)

theorem phi43PolyEmb_deg (κ : Kappa) (k : PolyIndex 2) :
    homogeneity κ (phi43PolyEmb k) = polyDeg 2 k := by
  rcases polyIndex_two_cases k with hk | hk | hk | hk
  · rw [phi43PolyEmb_eq_one hk]
    simp [homogeneity, polyDeg, hk, weight_parabolicWeight]
  · rw [phi43PolyEmb_eq_x0 hk]
    simp [homogeneity, polyDeg, hk, weight_parabolicWeight]
  · rw [phi43PolyEmb_eq_x1 hk]
    simp [homogeneity, polyDeg, hk, weight_parabolicWeight]
  · rw [phi43PolyEmb_eq_x2 hk]
    simp [homogeneity, polyDeg, hk, weight_parabolicWeight]

private theorem phi43_poly_coord_zero (g : G) (k : PolyIndex 2) {i : Symbol}
    (hi : i ∉ Set.range phi43PolyEmb) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single (phi43PolyEmb k) 1) i = 0 := by
  rcases polyIndex_two_cases k with hk | hk | hk | hk
  · have hone : i ≠ .one := by
      intro h
      apply hi
      exact ⟨k, (phi43PolyEmb_eq_one hk).trans h.symm⟩
    rw [phi43PolyEmb_eq_one hk]
    rw [phi43StructureGroupElement_apply_single]
    simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis, hone]
  · have hx : i ≠ .x 0 := by
      intro h
      apply hi
      exact ⟨k, (phi43PolyEmb_eq_x0 hk).trans h.symm⟩
    have hone : i ≠ .one := by
      intro h
      apply hi
      exact ⟨phi43PolyZero, phi43PolyEmb_zero.trans h.symm⟩
    rw [phi43PolyEmb_eq_x0 hk]
    rw [phi43StructureGroupElement_apply_single]
    simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis, hx, hone]
  · have hx : i ≠ .x 1 := by
      intro h
      apply hi
      exact ⟨k, (phi43PolyEmb_eq_x1 hk).trans h.symm⟩
    have hone : i ≠ .one := by
      intro h
      apply hi
      exact ⟨phi43PolyZero, phi43PolyEmb_zero.trans h.symm⟩
    rw [phi43PolyEmb_eq_x1 hk]
    rw [phi43StructureGroupElement_apply_single]
    simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis, hx, hone]
  · have hx : i ≠ .x 2 := by
      intro h
      apply hi
      exact ⟨k, (phi43PolyEmb_eq_x2 hk).trans h.symm⟩
    have hone : i ≠ .one := by
      intro h
      apply hi
      exact ⟨phi43PolyZero, phi43PolyEmb_zero.trans h.symm⟩
    rw [phi43PolyEmb_eq_x2 hk]
    rw [phi43StructureGroupElement_apply_single]
    simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis, hx, hone]

/-- The `N=2` polynomial sector, containing `1` and the spatial coordinates. -/
def phi43PolynomialSector (κ : Kappa) :
    PolynomialSector (phi43RegularityStructure κ) 2 where
  emb := phi43PolyEmb
  emb_injective := phi43PolyEmb_injective
  deg_emb := phi43PolyEmb_deg κ
  invariant := by
    rintro g ⟨p, rfl⟩ τ hτ i hi
    rw [eq_sum_single τ]
    simp only [map_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hσrange : σ ∈ Set.range phi43PolyEmb
    · obtain ⟨k, rfl⟩ := hσrange
      rw [map_smul, Pi.smul_apply]
      simp [phi43_poly_coord_zero p k hi]
    · simp [hτ σ hσrange]

theorem phi43PolynomialSector_emb (κ : Kappa) :
    (phi43PolynomialSector κ).emb = phi43PolyEmb := rfl

end RegularityStructures.Phi43

end
