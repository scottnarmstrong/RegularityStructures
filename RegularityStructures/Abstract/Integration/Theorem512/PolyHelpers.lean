/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.Integration.Commute
public import RegularityStructures.Abstract.Integration.KGamma
public import RegularityStructures.Abstract.Integration.Commute.Lemma516Integral

/-!
# Polynomial identities for Theorem 5.12

Finite sums of `regPi` (`Model.regPi_finset_sum`), evaluation of coefficient polynomials
(`polyEval_coeffPoly`), and `nVec` as an embedded polynomial (`nVec_eq_polyEmbed`), used for (5.17).

Source: [Hai14, Theorem 5.12].
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

theorem regPi_finset_sum (M : Model 𝒯 parabolicSemigroup) (x : ParabolicSpace) {J : Type*}
    (s : Finset J) (c : J → ℝ) (v : J → ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    M.regPi x (∑ j ∈ s, c j • v j) t z = ∑ j ∈ s, c j * M.regPi x (v j) t z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := M.regPi_smul x 0 0 t z
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, M.regPi_add, M.regPi_smul, ih]

end Model

theorem polyEval_coeffPoly (x : ParabolicSpace) (s : ℝ) (c : (Fin 4 →₀ ℕ) → ℝ)
    (hN' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < s → multiDeg k < N') (z : ParabolicSpace) :
    polyEval x (fun k : PolyIndex N' => if polyDeg N' k < s then c k.1 / multiFactorial k.1 else 0)
        z = ∑ k ∈ taylorIdx s,
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) * c k := by
  classical
  rw [polyEval_eq_sum]
  set F : (Fin 4 →₀ ℕ) → ℝ := fun l =>
    if (multiDeg l : ℝ) < s then
      (evalParabolic (MvPolynomial.monomial l 1) (z - x) / multiFact l) * c l
    else 0 with hF
  have h1 : ∀ k : PolyIndex N', (if polyDeg N' k < s then c k.1 / multiFactorial k.1 else 0) *
      evalParabolic (MvPolynomial.monomial k.1 1) (z - x) = F k.1 := by
    intro k
    have hd : polyDeg N' k = (multiDeg k.1 : ℝ) := rfl
    have hm : (multiFactorial k.1 : ℝ) = multiFact k.1 := by
      unfold multiFactorial multiFact; push_cast; rfl
    rw [hd, hF]
    dsimp only
    split_ifs
    · rw [hm]; ring
    · simp
  simp only [h1]
  have h2 : ∑ k : PolyIndex N', F k.1 = ∑ l ∈ Finset.univ.image (Subtype.val : PolyIndex N' → _),
      F l := (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
  rw [h2, ← Finset.sum_subset (s₁ := taylorIdx s)]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [hF]
    simp [(mem_taylorIdx_iff l).1 hl]
  · intro l hl
    refine Finset.mem_image.2 ⟨⟨l, ?_⟩, Finset.mem_univ _, rfl⟩
    exact hN' l ((mem_taylorIdx_iff l).1 hl)
  · intro l _ hl
    rw [hF]
    simp [(mem_taylorIdx_iff l).not.1 hl]

theorem nVec_eq_polyEmbed (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    nVec M N P γ f x = P.polyEmbed (fun k : PolyIndex N' =>
      if polyDeg N' k < γ + 2 then nCoeff M N f x k.1 / multiFactorial k.1 else 0) := by
  classical
  unfold nVec PolynomialSector.polyEmbed
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : polyDeg N' k < γ + 2 <;> simp [h]

end RegularityStructures

end
