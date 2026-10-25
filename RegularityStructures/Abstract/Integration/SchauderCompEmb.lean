/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderComp
public import RegularityStructures.Abstract.Integration.KGammaBound
public import RegularityStructures.Abstract.Integration.PolyCompat
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorPair

/-!
# Components of `J(x)` and `N_γ` on the polynomial sector

The coefficients of `jMap`, of `nVec` and of `Γ_{xy}` applied to `nVec` along the embedded
polynomial basis vectors (`jMap_apply_emb`, `nVec_apply_emb`, `gammaMap_nVec_apply_emb`).

Source: [Hai14, proof of Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem jMap_apply_emb (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (P : PolynomialSector 𝒯 N')
    (y : ParabolicSpace) (τ : ι → ℝ) (k : PolyIndex N') :
    jMap M N P y τ (P.emb k) = ∑ i, τ i * (if polyDeg N' k < 𝒯.deg i + 2 then
      jCoeff M N y i k.1 / multiFactorial k.1 else 0) := by
  classical
  simp only [jMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, jVec,
    smul_eq_mul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single k]
  · by_cases h : polyDeg N' k < 𝒯.deg i + 2 <;> simp [h]
  · intro c _ hc
    by_cases h : polyDeg N' c < 𝒯.deg i + 2 <;> simp [h, single_emb_apply, hc]
  · simp

theorem nVec_apply_emb (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (y : ParabolicSpace) (k : PolyIndex N') :
    nVec M N P γ f y (P.emb k) = if polyDeg N' k < γ + 2 then
      nCoeff M N f y k.1 / multiFactorial k.1 else 0 := by
  classical
  simp only [nVec, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · by_cases h : polyDeg N' k < γ + 2 <;> simp [h]
  · intro c _ hc
    by_cases h : polyDeg N' c < γ + 2 <;> simp [h, single_emb_apply, hc]
  · simp

theorem gammaMap_nVec_apply_emb {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (N : ℕ) (γ : ℝ) (f : ParabolicSpace → ι → ℝ)
    (x y : ParabolicSpace) (k : PolyIndex N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N') :
    M.gammaMap y x (nVec M N P γ f x) (P.emb k) * multiFactorial k.1 =
      ∑ l ∈ taylorIdx (γ + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        nCoeff M N f x (k.1 + l) := by
  classical
  set h := parabolicCoords (y - x) with hh
  have hcomp : ∀ l' : PolyIndex N', M.gammaMap y x (if polyDeg N' l' < γ + 2 then
      (nCoeff M N f x l'.1 / multiFactorial l'.1) • (Pi.single (P.emb l') 1 : ι → ℝ) else 0)
      (P.emb k) = if polyDeg N' l' < γ + 2 then (nCoeff M N f x l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (h i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
          else 0) else 0 := by
    intro l'
    by_cases hp : polyDeg N' l' < γ + 2
    · simp only [hp, ite_true, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [Model.gammaMap_single_emb hM y x l', Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, smul_eq_mul, single_emb_apply, ite_true, mul_one]
        rw [polyTranslate_single_apply]
      · intro m _ hm
        simp [single_emb_apply, hm]
      · simp
    · simp [hp]
  unfold nVec
  rw [map_sum, Finset.sum_apply]
  simp only [hcomp]
  set g : PolyIndex N' → ℝ := fun l' => (nCoeff M N f x l'.1 / multiFactorial l'.1) *
    ∏ i, (h i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ)) with hg
  have hsum : ∑ l' : PolyIndex N', (if polyDeg N' l' < γ + 2 then
      (nCoeff M N f x l'.1 / multiFactorial l'.1) *
        (if k.1 ≤ l'.1 then ∏ i, (h i ^ (l'.1 i - k.1 i) * ((l'.1 i).choose (k.1 i) : ℕ))
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
    have hc := coeff_translate_eq h k.1 (l'.1 - k.1)
    rw [← hl'1] at hc
    simp only [hg]
    rw [← hc]
    rw [← hl'1]
    ring

end RegularityStructures

end
