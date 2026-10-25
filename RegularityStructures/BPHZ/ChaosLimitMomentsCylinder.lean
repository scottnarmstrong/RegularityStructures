/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.WhiteNoiseChaosMoments

/-!
# Polynomials of finitely many values of a field that is a white-noise pairing

Let `ψ` be a random field such that every value `ψ(·, y)` is almost surely `W h_y` for a
square-integrable `h_y`. Then every polynomial of finitely many values `ψ(·, z_i)` is almost surely
a cylindrical polynomial of the white noise `W`, of the same total degree
(`exists_cylindrical_eval_ae`).

* `chaosPolyAt a P`: the one-variable polynomial `P` evaluated at the coordinate `X a`.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace RegularityStructures

/-- The one-variable polynomial `P` evaluated at the coordinate `X a` of a multivariate
polynomial ring. -/
def chaosPolyAt {ι : Type*} (a : ι) (P : Polynomial ℝ) : MvPolynomial ι ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i) * X a ^ i

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

/-- Evaluating `chaosPolyAt a P` evaluates `P` at the coordinate `a`. -/
theorem eval_chaosPolyAt {ι : Type*} (x : ι → ℝ) (a : ι) (P : Polynomial ℝ) :
    eval x (chaosPolyAt a P) = P.eval (x a) := by
  rw [Polynomial.eval_eq_sum_range]
  simp [chaosPolyAt, map_sum]

/-- The total degree of `chaosPolyAt a P` is at most the degree of `P`. -/
theorem totalDegree_chaosPolyAt_le {ι : Type*} (a : ι) (P : Polynomial ℝ) :
    (chaosPolyAt a P).totalDegree ≤ P.natDegree := by
  refine totalDegree_finsetSum_le fun i hi => ?_
  refine (totalDegree_mul _ _).trans ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have : (X a ^ i : MvPolynomial ι ℝ).totalDegree ≤ i := by
    refine (totalDegree_pow _ _).trans ?_
    simp
  simpa using this.trans hi'

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Polynomials of finitely many values of a white-noise field are cylindrical.**
If every value `ψ(·, y)` is almost surely `W h_y` with `h_y ∈ L²`, then `q(ψ(z₁), …, ψ(zₙ))`
is almost surely a cylindrical polynomial of `W` of total degree at most that of `q`. -/
theorem exists_cylindrical_eval_ae {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ψ : Ω → SpaceTime → ℝ}
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h)
    {ι : Type*} [Fintype ι] (z : ι → SpaceTime) (q : MvPolynomial ι ℝ) :
    ∃ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) ∧
      ∃ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ q.totalDegree ∧
        (fun ω => eval (fun i => ψ ω (z i)) q) =ᵐ[P] fun ω => eval (fun j => W (h j) ω) f := by
  choose hch hmem hae using hψW
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => hch (z (e.symm j)), fun j => hmem _, rename e q,
    totalDegree_rename_le _ _ |>.trans le_rfl, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, ψ ω (z i) = W (hch (z i)) ω := ae_all_iff.2 fun i => hae (z i)
  filter_upwards [hall] with ω hω
  rw [eval_rename]
  have hfun : (fun i => ψ ω (z i)) = (fun j => W (hch (z (e.symm j))) ω) ∘ e := by
    funext i
    simp [hω]
  rw [hfun]

end RegularityStructures

end
