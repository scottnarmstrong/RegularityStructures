/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Witness
public import RegularityStructures.Abstract.Polynomial.Model.Unit
public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# The non-integrality hypothesis on the polynomial structure

The non-integrality hypothesis `hni` of [Hai14, Theorem 7.1] and of the `Φ⁴₃` fixed point asks
`|k|_𝔰 ≠ deg τ + 2` for the indices `τ` of degree in `[ζ, γ̄)`. If it ranges over all indices, it
also quantifies over the polynomial index `X⁰` (degree `0`) and `k = X₀` (`|k|_𝔰 = 2`), so it is
false whenever `ζ ≤ 0 < γ̄` (`Regression.hni_allIndices_false`). Restricted to the non-polynomial
indices (`i ∉ range P.emb`), the form the library uses, it is satisfiable in that situation: on the
polynomial structure all indices are polynomial, and the restricted hypothesis holds trivially
(`Regression.hni_nonPolynomial_polynomialStructure`), while the unrestricted one fails
(`Regression.hni_allIndices_false_polynomialStructure`).
-/

open RegularityStructures

theorem Regression.hni_allIndices_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {N' : ℕ} (Ppoly : PolynomialSector 𝒯 N') (hN' : 0 < N') {ζ γb : ℝ}
    (hζ : ζ ≤ 0) (hγ : 0 < γb) :
    ¬ (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γb + 2 →
      ∀ i, ζ ≤ 𝒯.deg i → 𝒯.deg i < γb → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) := by
  intro h
  have hk : (multiDeg (Finsupp.single (0 : Fin 4) 1) : ℝ) = 2 := by
    simp [multiDeg, parabolicWeight, Finsupp.weight_single]
  have hdeg : 𝒯.deg (Ppoly.emb (polyZero hN')) = 0 := by
    rw [Ppoly.deg_emb, polyDeg_polyZero]
  exact h (Finsupp.single (0 : Fin 4) 1) (by rw [hk]; linarith) (Ppoly.emb (polyZero hN'))
    (by rw [hdeg]; exact hζ) (by rw [hdeg]; exact hγ) (by rw [hk, hdeg]; norm_num)

/-- The restricted `hni` holds for the polynomial structure, for every `ζ` and `γ̄`, in particular
for `ζ ≤ 0 < γ̄`, where the unrestricted `hni` is false. -/
theorem Regression.hni_nonPolynomial_polynomialStructure (N' : ℕ) (ζ γb : ℝ) :
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γb + 2 →
      ∀ i, i ∉ Set.range (polySector N').emb → ζ ≤ (polynomialStructure N').deg i →
        (polynomialStructure N').deg i < γb → (multiDeg k : ℝ) ≠ (polynomialStructure N').deg i + 2 :=
  fun _ _ i hi => absurd ⟨i, rfl⟩ hi

theorem Regression.hni_allIndices_false_polynomialStructure (N' : ℕ) (hN' : 0 < N') {ζ γb : ℝ}
    (hζ : ζ ≤ 0) (hγ : 0 < γb) :
    ¬ (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γb + 2 →
      ∀ i, ζ ≤ (polynomialStructure N').deg i → (polynomialStructure N').deg i < γb →
        (multiDeg k : ℝ) ≠ (polynomialStructure N').deg i + 2) :=
  Regression.hni_allIndices_false (polySector N') hN' hζ hγ
