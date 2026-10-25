/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Basic
public import RegularityStructures.Abstract.Polynomial.Coeff
public import RegularityStructures.Abstract.RegularityStructure

/-!
# Translations on the polynomial model space

The structure group of the polynomial regularity structure consists of the translations
`Γ_h X^k = (X + h)^k` [Hai14, Section 2.2, Remark 2.23]. Here `translateAlg h` is the substitution
`X_i ↦ X_i + h_i` on `MvPolynomial (Fin 4) ℝ`, and `polyTranslate h` is its compression to
`PolyIndex N → ℝ`. Translations do not raise the parabolic degree and fix the top homogeneous
part, so they are graded unipotent (`isGradedUnipotent_polyTranslate`) and form a group
(`polyTranslate_zero`, `polyTranslate_add`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

open MvPolynomial

/-- The substitution `X_i ↦ X_i + h_i` as an algebra endomorphism of the polynomial ring. -/
def translateAlg (h : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ :=
  aeval fun i => X i + C (h i)

/-- The translation `Γ_h : X^k ↦ (X + h)^k` of the model space `PolyIndex N → ℝ`. -/
def polyTranslate {N : ℕ} (h : Fin 4 → ℝ) : (PolyIndex N → ℝ) →ₗ[ℝ] (PolyIndex N → ℝ) :=
  ofPoly N ∘ₗ (translateAlg h).toLinearMap ∘ₗ toPoly N

end RegularityStructures

end

public section

namespace RegularityStructures

open MvPolynomial

variable {N : ℕ}

theorem translateAlg_monomial (h : Fin 4 → ℝ) (k : Fin 4 →₀ ℕ) :
    translateAlg h (monomial k 1) = ∏ i, (X i + C (h i) : MvPolynomial (Fin 4) ℝ) ^ k i := by
  rw [translateAlg, aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

theorem coeff_translateAlg_monomial (h : Fin 4 → ℝ) (k l : Fin 4 →₀ ℕ) :
    (translateAlg h (monomial k 1)).coeff l =
      if l ≤ k then ∏ i, h i ^ (k i - l i) * ((k i).choose (l i) : ℝ) else 0 := by
  rw [translateAlg_monomial, coeff_prod_X_add_C_pow]

theorem polyTranslate_single_apply (h : Fin 4 → ℝ) (k l : PolyIndex N) :
    polyTranslate h (Pi.single k 1) l =
      if l.1 ≤ k.1 then ∏ i, h i ^ (k.1 i - l.1 i) * ((k.1 i).choose (l.1 i) : ℝ) else 0 := by
  simp [polyTranslate, toPoly_single, ofPoly_apply, coeff_translateAlg_monomial]

theorem weight_le_of_le {k l : Fin 4 →₀ ℕ} (h : l ≤ k) :
    Finsupp.weight parabolicWeight l ≤ Finsupp.weight parabolicWeight k := by
  rw [weight_parabolicWeight, weight_parabolicWeight]
  have := Finsupp.le_def.1 h
  have h0 := this 0
  have h1 := this 1
  have h2 := this 2
  have h3 := this 3
  omega

theorem eq_of_le_of_weight_le {k l : Fin 4 →₀ ℕ} (h : l ≤ k)
    (hw : Finsupp.weight parabolicWeight k ≤ Finsupp.weight parabolicWeight l) : l = k := by
  rw [weight_parabolicWeight, weight_parabolicWeight] at hw
  have := Finsupp.le_def.1 h
  have h0 := this 0
  have h1 := this 1
  have h2 := this 2
  have h3 := this 3
  refine Finsupp.ext fun i => ?_
  fin_cases i <;> simp <;> omega

theorem coeff_translateAlg_toPoly_of_le (h : Fin 4 → ℝ) (τ : PolyIndex N → ℝ)
    {l : Fin 4 →₀ ℕ} (hl : N ≤ Finsupp.weight parabolicWeight l) :
    (translateAlg h (toPoly N τ)).coeff l = 0 := by
  rw [toPoly_apply, map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, coeff_smul, coeff_translateAlg_monomial]
  split_ifs with hlk
  · have := weight_le_of_le hlk
    have := k.2
    omega
  · simp

/-- The compression `polyTranslate` intertwines with the substitution `translateAlg`. -/
theorem toPoly_polyTranslate (h : Fin 4 → ℝ) (τ : PolyIndex N → ℝ) :
    toPoly N (polyTranslate h τ) = translateAlg h (toPoly N τ) :=
  toPoly_ofPoly fun _ hl => coeff_translateAlg_toPoly_of_le h τ hl

theorem translateAlg_zero : translateAlg 0 = AlgHom.id ℝ (MvPolynomial (Fin 4) ℝ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [translateAlg]

theorem translateAlg_add (h h' : Fin 4 → ℝ) :
    (translateAlg h).comp (translateAlg h') = translateAlg (h + h') := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [translateAlg, add_assoc]

theorem polyTranslate_zero : (polyTranslate 0 : (PolyIndex N → ℝ) →ₗ[ℝ] (PolyIndex N → ℝ)) =
    LinearMap.id := by
  refine LinearMap.ext fun τ => ?_
  simp [polyTranslate, translateAlg_zero, ofPoly_toPoly]

theorem polyTranslate_add (h h' : Fin 4 → ℝ) :
    (polyTranslate h ∘ₗ polyTranslate h' : (PolyIndex N → ℝ) →ₗ[ℝ] (PolyIndex N → ℝ)) =
      polyTranslate (h + h') := by
  refine LinearMap.ext fun τ => ?_
  have e : polyTranslate h (polyTranslate h' τ) =
      ofPoly N (translateAlg h (toPoly N (polyTranslate h' τ))) := rfl
  rw [LinearMap.comp_apply, e, toPoly_polyTranslate, ← AlgHom.comp_apply, translateAlg_add]
  rfl

/-- Translations are graded unipotent: `Γ_h X^k - X^k` only involves `X^l` with `|l|_𝔰 < |k|_𝔰`. -/
theorem isGradedUnipotent_polyTranslate (h : Fin 4 → ℝ) :
    IsGradedUnipotent (polyDeg N) (polyTranslate h) := by
  intro k l hkl
  have hkl' : Finsupp.weight parabolicWeight k.1 ≤ Finsupp.weight parabolicWeight l.1 := by
    simpa [polyDeg] using hkl
  rw [Pi.sub_apply, polyTranslate_single_apply]
  by_cases hle : l.1 ≤ k.1
  · have := eq_of_le_of_weight_le hle hkl'
    have hlk : l = k := Subtype.ext this
    subst hlk
    simp
  · simp only [hle, ite_false, zero_sub, neg_eq_zero]
    exact Pi.single_eq_of_ne (fun e => hle (by subst e; exact le_rfl)) _

end RegularityStructures

end
