/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.QuadraticPolynomialIndex
import Mathlib.Tactic.FinCases

/-!
# The degree≤2 polynomial sector of the finite Phi4 structure

The polynomial cutoff 3 includes time and commutative spatial quadratics,
as needed by the Phi4 fixed point [Hai14, Section 9.4, Proposition 9.8].
The existing cutoff-2 polynomial sector remains unchanged.
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem phi43QuadraticPolyEmb_cases (k : PolyIndex 3) :
    phi43QuadraticPolyEmb k = .one ∨ phi43QuadraticPolyEmb k = .x0 ∨
      (∃ i, phi43QuadraticPolyEmb k = .x i) ∨ (∃ p, phi43QuadraticPolyEmb k = .xMul p) := by
  unfold phi43QuadraticPolyEmb phi43QuadraticSymbolOfIndex
  split_ifs
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

private def polyZero : PolyIndex 3 := ⟨0, by simp⟩
private def polyTime : PolyIndex 3 := ⟨Finsupp.single 0 1, by norm_num [weight_parabolicWeight]⟩
private def polySpace (i : Fin 3) : PolyIndex 3 :=
  ⟨Finsupp.single i.succ 1, by fin_cases i <;> norm_num [weight_parabolicWeight]⟩
private def polyPair (i j : Fin 3) : PolyIndex 3 :=
  ⟨Finsupp.single i.succ 1 + Finsupp.single j.succ 1,
    by fin_cases i <;> fin_cases j <;> norm_num [weight_parabolicWeight]⟩

private theorem emb_zero : phi43QuadraticPolyEmb polyZero = .one := by
  norm_num [phi43QuadraticPolyEmb, phi43QuadraticSymbolOfIndex, polyZero]

private theorem emb_time : phi43QuadraticPolyEmb polyTime = .x0 := by
  norm_num [phi43QuadraticPolyEmb, phi43QuadraticSymbolOfIndex, polyTime, Finsupp.single_apply]

private theorem emb_space (i : Fin 3) : phi43QuadraticPolyEmb (polySpace i) = .x i := by
  fin_cases i <;>
    norm_num [phi43QuadraticPolyEmb, phi43QuadraticSymbolOfIndex, polySpace, Finsupp.single_apply]

private theorem emb_pair (i j : Fin 3) : phi43QuadraticPolyEmb (polyPair i j) = .xMul s(i, j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [phi43QuadraticPolyEmb, phi43QuadraticSymbolOfIndex, polyPair,
      Finsupp.single_apply, Sym2.eq_iff]

theorem phi43QuadraticPolyEmb_range (τ : Symbol) :
    τ ∈ Set.range phi43QuadraticPolyEmb ↔
      τ = .one ∨ τ = .x0 ∨ (∃ i, τ = .x i) ∨ (∃ p, τ = .xMul p) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact phi43QuadraticPolyEmb_cases k
  · rintro (rfl | rfl | ⟨i, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨polyZero, emb_zero⟩
    · exact ⟨polyTime, emb_time⟩
    · exact ⟨polySpace i, emb_space i⟩
    · induction p using Sym2.inductionOn with
      | _ i j => exact ⟨polyPair i j, emb_pair i j⟩

private theorem poly_coord_zero (g : G) (τ : Symbol)
    (hτ : τ ∈ Set.range phi43QuadraticPolyEmb) {σ : Symbol}
    (hσ : σ ∉ Set.range phi43QuadraticPolyEmb) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single τ 1) σ = 0 := by
  have h1 : σ ≠ .one := fun h => hσ ((phi43QuadraticPolyEmb_range σ).2 (Or.inl h))
  have ht : σ ≠ .x0 := fun h => hσ ((phi43QuadraticPolyEmb_range σ).2 (Or.inr (Or.inl h)))
  have hx (i : Fin 3) : σ ≠ .x i := fun h =>
    hσ ((phi43QuadraticPolyEmb_range σ).2 (Or.inr (Or.inr (Or.inl ⟨i, h⟩))))
  have hxx (p : Sym2 (Fin 3)) : σ ≠ .xMul p := fun h =>
    hσ ((phi43QuadraticPolyEmb_range σ).2 (Or.inr (Or.inr (Or.inr ⟨p, h⟩))))
  rw [phi43StructureGroupElement_apply_single]
  rcases (phi43QuadraticPolyEmb_range τ).1 hτ with rfl | rfl | ⟨i, rfl⟩ | ⟨p, rfl⟩
  all_goals try simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis, h1, ht, hx]
  induction p using Sym2.inductionOn with
  | _ i j =>
    simp [xMulAction_mk, primitiveAction, multiply_add_left, multiply_add_right,
      basisProduct, productSymbol, basis, h1, hx, hxx]

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The polynomial sector of parabolic degree≤2, with strict cutoff 3. -/
def phi43PolynomialSectorQuadratic (κ : Kappa) :
    PolynomialSector (phi43RegularityStructure κ) 3 where
  emb := phi43QuadraticPolyEmb
  emb_injective := phi43QuadraticPolyEmb_injective
  deg_emb := phi43QuadraticPolyEmb_deg κ
  invariant := by
    rintro g ⟨p, rfl⟩ a ha σ hσ
    rw [eq_sum_single a]
    simp only [map_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτ : τ ∈ Set.range phi43QuadraticPolyEmb
    · rw [map_smul, Pi.smul_apply]
      simp [poly_coord_zero p τ hτ hσ]
    · simp [ha τ hτ]

end RegularityStructures.Phi43

end
