/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderComp
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The polynomial components of `Γ_{yx} I e_i`

For a model realising the kernel with profile `h`, Hairer's Lemma 5.16 in the form
`Γ_{yx} (I + J(x)) e_i = (I + J(y)) Γ_{yx} e_i` gives, for `I` without `T̄` components on `V`,
`k! (Γ_{yx} I e_i)_{X^k} = ∑_j τ_j [|k| < deg j + 2] J_{y,j,k} − ∑_{|l| < deg i + 2 − |k|}
 (y−x)^l/l! J_{x,i,k+l}`, `τ = Γ_{yx} e_i`, `J_{x,j,k} = jCoeffP M h x j k`
(`Model.gammaMap_integral_apply_emb`).  This is the starting point of
[Hai14, Lemma 5.21] for the polynomial components `Jxy` of the extension `Γ̂`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

theorem gammaMap_jVecP_apply_emb {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (h : ParabolicSpace → ℝ) (i : ι) (x y : ParabolicSpace)
    (k : PolyIndex N')
    (hN : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < 𝒯.deg i + 2 → multiDeg l < N') :
    M.gammaMap y x (jVecP M h P x i) (P.emb k) * multiFactorial k.1 =
      ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        jCoeffP M h x i (k.1 + l) := by
  classical
  set h' := parabolicCoords (y - x) with hh
  have hcomp : ∀ l' : PolyIndex N', M.gammaMap y x (if polyDeg N' l' < 𝒯.deg i + 2 then
      (jCoeffP M h x i l'.1 / multiFactorial l'.1) • (Pi.single (P.emb l') 1 : ι → ℝ) else 0)
      (P.emb k) = if polyDeg N' l' < 𝒯.deg i + 2 then
        (jCoeffP M h x i l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (h' i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
          else 0) else 0 := by
    intro l'
    by_cases hp : polyDeg N' l' < 𝒯.deg i + 2
    · simp only [hp, ite_true, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [Model.gammaMap_single_emb hM y x l', Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, smul_eq_mul, single_emb_apply, ite_true, mul_one]
        rw [polyTranslate_single_apply]
      · intro m _ hm
        simp [single_emb_apply, hm]
      · simp
    · simp [hp]
  unfold jVecP
  rw [map_sum, Finset.sum_apply]
  simp only [hcomp]
  set g : PolyIndex N' → ℝ := fun l' => (jCoeffP M h x i l'.1 / multiFactorial l'.1) *
    ∏ i, (h' i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ)) with hg
  have hsum : ∑ l' : PolyIndex N', (if polyDeg N' l' < 𝒯.deg i + 2 then
      (jCoeffP M h x i l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (h' i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
          else 0) else 0) =
      ∑ l' ∈ Finset.univ.filter (fun l' : PolyIndex N' =>
        polyDeg N' l' < 𝒯.deg i + 2 ∧ k.1 ≤ l'.1), g l' := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l' _ => ?_
    by_cases hp : polyDeg N' l' < 𝒯.deg i + 2 <;> by_cases hk : k.1 ≤ l'.1 <;>
      simp [hp, hk, hg]
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_bij' (fun l' _ => l'.1 - k.1)
    (fun l hl => (⟨k.1 + l, ?_⟩ : PolyIndex N')) ?_ ?_ ?_ ?_ ?_
  · have hl' := (mem_taylorIdx_iff _).1 hl
    have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
    have : (multiDeg (k.1 + l) : ℝ) < 𝒯.deg i + 2 := by
      rw [hadd]; push_cast; linarith
    exact hN _ this
  · intro l' hl'
    obtain ⟨hp, hkl⟩ := Finset.mem_filter.1 hl' |>.2
    rw [mem_taylorIdx_iff]
    have hw := weight_add_tsub hkl
    have : (multiDeg (l'.1 - k.1) : ℝ) = multiDeg l'.1 - multiDeg k.1 := by
      have : multiDeg l'.1 = multiDeg k.1 + multiDeg (l'.1 - k.1) := hw
      rw [this]; push_cast; ring
    rw [this]
    have hp' : (multiDeg l'.1 : ℝ) < 𝒯.deg i + 2 := hp
    linarith
  · intro l hl
    have hl' := (mem_taylorIdx_iff _).1 hl
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
      show ((Finsupp.weight parabolicWeight (k.1 + l) : ℕ) : ℝ) < 𝒯.deg i + 2
      change (multiDeg (k.1 + l) : ℝ) < 𝒯.deg i + 2
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
    have hc := coeff_translate_eq h' k.1 (l'.1 - k.1)
    rw [← hl'1] at hc
    simp only [hg]
    rw [← hc]
    rw [← hl'1]
    ring

end RegularityStructures

end
