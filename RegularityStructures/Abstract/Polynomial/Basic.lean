/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Polynomial
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Fintype.Pi

/-!
# The polynomial regularity structure: model space

The model space of the polynomial regularity structure `T̄_N` on `ℝ⁴` with parabolic scaling
[Hai14, Section 2.2, Remark 2.23] has the basis `X^k`, for the multi-indices `k` of parabolic degree
`|k|_𝔰 = 2 k₀ + k₁ + k₂ + k₃ < N`, with `deg X^k = |k|_𝔰`. Here `PolyIndex N` is the type of these
multi-indices, `toPoly` identifies `PolyIndex N → ℝ` with polynomials in four variables, and
`ofPoly` reads off coefficients.

Source: [Hai14] = arXiv:1303.5113v4.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The multi-indices `k` of parabolic degree `|k|_𝔰 < N`: the basis of the polynomial
regularity structure. -/
abbrev PolyIndex (N : ℕ) : Type := {k : Fin 4 →₀ ℕ // Finsupp.weight parabolicWeight k < N}

/-- The homogeneity `|X^k|_𝔰 = 2 k₀ + k₁ + k₂ + k₃` of the basis vector `X^k`. -/
def polyDeg (N : ℕ) : PolyIndex N → ℝ := fun k => (Finsupp.weight parabolicWeight k.1 : ℝ)

end RegularityStructures

end

public section

namespace RegularityStructures

variable {N : ℕ}

theorem coord_lt_of_weight_lt {k : Fin 4 →₀ ℕ} (hk : Finsupp.weight parabolicWeight k < N)
    (i : Fin 4) : k i < N := by
  rw [weight_parabolicWeight] at hk
  fin_cases i <;> simp <;> omega

theorem finite_polyIndex (N : ℕ) : Finite (PolyIndex N) := by
  refine Finite.of_injective
    (fun k : PolyIndex N => fun i : Fin 4 => (⟨k.1 i, coord_lt_of_weight_lt k.2 i⟩ : Fin N)) ?_
  intro a b hab
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  simpa using congrFun hab i

noncomputable instance (N : ℕ) : Fintype (PolyIndex N) :=
  haveI := finite_polyIndex N
  Fintype.ofFinite _

end RegularityStructures

end

@[expose] public noncomputable section

namespace RegularityStructures

variable {N : ℕ}

/-- The polynomial `∑ τ_k X^k` with coefficient vector `τ`. -/
def toPoly (N : ℕ) : (PolyIndex N → ℝ) →ₗ[ℝ] MvPolynomial (Fin 4) ℝ where
  toFun τ := ∑ k, τ k • MvPolynomial.monomial k.1 (1 : ℝ)
  map_add' τ σ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c τ := by simp [Finset.smul_sum, mul_smul]

/-- The coefficient vector of a polynomial, with the coefficients of degree `≥ N` forgotten. -/
def ofPoly (N : ℕ) : MvPolynomial (Fin 4) ℝ →ₗ[ℝ] (PolyIndex N → ℝ) where
  toFun p k := p.coeff k.1
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp

end RegularityStructures

end

public section

namespace RegularityStructures

variable {N : ℕ}

theorem toPoly_apply (τ : PolyIndex N → ℝ) :
    toPoly N τ = ∑ k, τ k • MvPolynomial.monomial k.1 (1 : ℝ) := rfl

theorem ofPoly_apply (p : MvPolynomial (Fin 4) ℝ) (k : PolyIndex N) :
    ofPoly N p k = p.coeff k.1 := rfl

theorem coeff_toPoly (τ : PolyIndex N → ℝ) (l : Fin 4 →₀ ℕ) :
    (toPoly N τ).coeff l = if h : Finsupp.weight parabolicWeight l < N then τ ⟨l, h⟩ else 0 := by
  rw [toPoly_apply, MvPolynomial.coeff_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨l, h⟩]
    · simp [MvPolynomial.coeff_monomial]
    · intro k _ hk
      have : k.1 ≠ l := fun e => hk (Subtype.ext e)
      simp [MvPolynomial.coeff_monomial, this]
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    have : k.1 ≠ l := fun e => h (e ▸ k.2)
    simp [MvPolynomial.coeff_monomial, this]

/-- `ofPoly ∘ toPoly = id`. -/
theorem ofPoly_toPoly (τ : PolyIndex N → ℝ) : ofPoly N (toPoly N τ) = τ := by
  ext k
  simp [ofPoly_apply, coeff_toPoly, k.2]

/-- `toPoly ∘ ofPoly = id` on polynomials of parabolic degree `< N`. -/
theorem toPoly_ofPoly {p : MvPolynomial (Fin 4) ℝ}
    (hp : ∀ l, N ≤ Finsupp.weight parabolicWeight l → p.coeff l = 0) :
    toPoly N (ofPoly N p) = p := by
  ext l
  rw [coeff_toPoly]
  split_ifs with h
  · rfl
  · exact (hp l (not_lt.1 h)).symm

theorem toPoly_single (k : PolyIndex N) :
    toPoly N (Pi.single k 1) = MvPolynomial.monomial k.1 (1 : ℝ) := by
  simp [toPoly_apply, Pi.single_apply]

end RegularityStructures

end
