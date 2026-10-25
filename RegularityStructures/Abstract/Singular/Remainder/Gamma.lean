/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Emb
public import RegularityStructures.Abstract.Singular.Remainder.Defs
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The `X^k`-components of `R_γ f(x)` and of `Γ_{yx} R_γ f(x)`

Analogues of `nVecS_apply_emb`, `nVecS_mem_subspace` and `gammaMap_nVecS_apply_emb`
(`RegularityStructures.Abstract.Singular.KGamma.Emb`) for `Model.remVec`: `Γ_{yx} R_γ f(x)` has
`X^k`-coefficient `(1/k!) ∑_l (y − x)^l/l! ⟨R f, D^{k+l} R(x − ·)⟩`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

open Classical in
/-- The `X^k`-components of `Γ_{yx}` applied to a polynomial vector with coefficients `a`. -/
theorem gammaMap_polyVec_apply_emb {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (γ : ℝ) (a : (Fin 4 →₀ ℕ) → ℝ)
    (x y : ParabolicSpace) (k : PolyIndex N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N') :
    M.gammaMap y x (∑ k' : PolyIndex N', if polyDeg N' k' < γ + 2 then
      (a k'.1 / multiFactorial k'.1) • (Pi.single (P.emb k') 1 : ι → ℝ) else 0) (P.emb k) *
        multiFactorial k.1 =
      ∑ l ∈ taylorIdx (γ + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        a (k.1 + l) := by
  classical
  set c := parabolicCoords (y - x) with hc
  have hcomp : ∀ l' : PolyIndex N', M.gammaMap y x (if polyDeg N' l' < γ + 2 then
      (a l'.1 / multiFactorial l'.1) • (Pi.single (P.emb l') 1 : ι → ℝ) else 0)
      (P.emb k) = if polyDeg N' l' < γ + 2 then (a l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (c i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
          else 0) else 0 := by
    intro l'
    by_cases hp : polyDeg N' l' < γ + 2
    · simp only [hp, ite_true, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [gammaMap_single_emb hM y x l', Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, smul_eq_mul, single_emb_apply, ite_true, mul_one]
        rw [polyTranslate_single_apply]
      · intro m _ hm
        simp [single_emb_apply, hm]
      · simp
    · simp [hp]
  rw [map_sum, Finset.sum_apply]
  simp only [hcomp]
  set g : PolyIndex N' → ℝ := fun l' => (a l'.1 / multiFactorial l'.1) *
    ∏ i, (c i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ)) with hg
  have hsum : ∑ l' : PolyIndex N', (if polyDeg N' l' < γ + 2 then
      (a l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (c i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
          else 0) else 0) =
      ∑ l' ∈ Finset.univ.filter (fun l' : PolyIndex N' => polyDeg N' l' < γ + 2 ∧ k.1 ≤ l'.1),
        g l' := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l' _ => ?_
    by_cases hp : polyDeg N' l' < γ + 2 <;> by_cases hk : k.1 ≤ l'.1 <;> simp [hp, hk, hg]
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_bij' (fun l' _ => l'.1 - k.1)
    (fun l hl => (⟨k.1 + l, ?_⟩ : PolyIndex N')) ?_ ?_ ?_ ?_ ?_
  · have hl' := (mem_taylorIdx_iff _).1 hl
    have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
    have : (multiDeg (k.1 + l) : ℝ) < γ + 2 := by
      rw [hadd]; push_cast; linarith
    exact hNγ _ this
  · intro l' hl'
    obtain ⟨hp, hkl⟩ := Finset.mem_filter.1 hl' |>.2
    rw [mem_taylorIdx_iff]
    have hw := weight_add_tsub hkl
    have : (multiDeg (l'.1 - k.1) : ℝ) = multiDeg l'.1 - multiDeg k.1 := by
      have : multiDeg l'.1 = multiDeg k.1 + multiDeg (l'.1 - k.1) := hw
      rw [this]; push_cast; ring
    rw [this]
    have hp' : (multiDeg l'.1 : ℝ) < γ + 2 := hp
    linarith
  · intro l hl
    have hl' := (mem_taylorIdx_iff _).1 hl
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
      show ((Finsupp.weight parabolicWeight (k.1 + l) : ℕ) : ℝ) < γ + 2
      change (multiDeg (k.1 + l) : ℝ) < γ + 2
      rw [hadd]; push_cast; linarith
    · exact le_self_add
  · intro l' hl'
    obtain ⟨hp, hkl⟩ := Finset.mem_filter.1 hl' |>.2
    exact Subtype.ext (add_tsub_cancel_of_le hkl)
  · intro l hl
    simp
  · intro l' hl'
    obtain ⟨hp, hkl⟩ := Finset.mem_filter.1 hl' |>.2
    have hl'1 : l'.1 = k.1 + (l'.1 - k.1) := (add_tsub_cancel_of_le hkl).symm
    have hc := coeff_translate_eq c k.1 (l'.1 - k.1)
    rw [← hl'1] at hc
    simp only [hg]
    rw [← hc]
    rw [← hl'1]
    ring

end Model

end RegularityStructures

end
