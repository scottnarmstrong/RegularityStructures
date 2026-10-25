/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.JSum
public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinearG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# The map `J⊕(x)` of the difference model under weighted bounds

Weighted versions (`Model.GrowthModel` of `M₁`, `M₂`) of `jVecP_modelSum_inl` and
`jMapP_modelSum_liftVec` of `RegularityStructures.Abstract.Singular.TwoModel.JSum` (the `inr`
statements and `jMapP_eq_of_mem_subspace` do not involve bounds): for `u ∈ V ∩ T_{<γ}`,
`J⊕(x) (λ Q u, u - v) = (0, J¹(x) u - J²(x) v)`.
-/

public section

open Set

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}
  {γ CPi₁ CGam₁ CPi₂ CGam₂ p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

theorem jVecP_modelSum_inl_growth (hh : ShellProfile h N) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) 
    (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) (i : NonPoly P)
    (hVi : (Pi.single i.1 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i.1 < γ) (x : ParabolicSpace) :
    leftPart P (jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inl i)) = 0 ∧
      rightPart P (jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inl i)) =
        lam⁻¹ • (jVecP M₁ h P x i.1 - jVecP M₂ h P x i.1) := by
  classical
  unfold jVecP
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun kk _ => ?_
    split_ifs
    · change leftPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = 0
      rw [map_smul, leftPart_single_inr, smul_zero]
    · exact map_zero _
  · rw [map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : polyDeg N' kk < (structSumU P).deg (Sum.inl i) + 2
    · have hk' : (multiDeg kk.1 : ℝ) < 𝒯.deg i.1 + 2 := hk
      have hk'' : polyDeg N' kk < 𝒯.deg i.1 + 2 := hk
      simp only [hk, hk'', ite_true]
      change rightPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = _
      rw [map_smul, rightPart_single_inr,
        jCoeffP_modelSum_inl_growth hh h₁ h₂ hV hVb G₁ G₂ hdeg i hVi hi x hk']
      module
    · have hk'' : ¬ polyDeg N' kk < 𝒯.deg i.1 + 2 := hk
      simp [hk, hk'']

theorem jMapP_modelSum_liftVec_growth (hh : ShellProfile h N) (hlam : lam ≠ 0)
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) 
    (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) (x : ParabolicSpace)
    {u v : ι → ℝ} (hu : u ∈ V) (huγ : u ∈ lowerSubspace 𝒯.deg γ) :
    leftPart P (jMapP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (liftVec P lam u v)) = 0 ∧
      rightPart P (jMapP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x
        (liftVec P lam u v)) = jMapP M₁ h P x u - jMapP M₂ h P x v := by
  classical
  have hli : ∀ i : NonPoly P, u i.1 ≠ 0 →
      (Pi.single i.1 1 : ι → ℝ) ∈ V ∧ 𝒯.deg i.1 < γ := fun i hu0 =>
    ⟨hVb u hu i.1 hu0, by
      by_contra hc
      exact hu0 (huγ i.1 (not_lt.1 hc))⟩
  have hl : ∀ s : NonPoly P ⊕ ι, leftPart P (liftVec P lam u v s •
      jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x s) = 0 := by
    intro s
    rw [map_smul]
    rcases s with i | j
    · by_cases hi : u i.1 = 0
      · have : liftVec P lam u v (Sum.inl i) = 0 := by
          change lam * restrictNP P u i = 0
          rw [restrictNP_apply, hi, mul_zero]
        rw [this, zero_smul]
      · obtain ⟨hVi, hdi⟩ := hli i hi
        rw [(jVecP_modelSum_inl_growth hh h₁ h₂ hV hVb G₁ G₂ hdeg i hVi hdi
          x).1, smul_zero]
    · rw [(jVecP_modelSum_inr h₁ h₂ j x).1, smul_zero]
  have hr : ∀ i : NonPoly P, rightPart P (liftVec P lam u v (Sum.inl i) •
      jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inl i)) =
      u i.1 • (jVecP M₁ h P x i.1 - jVecP M₂ h P x i.1) := by
    intro i
    rw [map_smul]
    by_cases hi : u i.1 = 0
    · have : liftVec P lam u v (Sum.inl i) = 0 := by
        change lam * restrictNP P u i = 0
        rw [restrictNP_apply, hi, mul_zero]
      rw [this, zero_smul, hi, zero_smul]
    · obtain ⟨hVi, hdi⟩ := hli i hi
      rw [(jVecP_modelSum_inl_growth hh h₁ h₂ hV hVb G₁ G₂ hdeg i hVi hdi
        x).2]
      change (lam * u i.1) • lam⁻¹ • _ = _
      rw [smul_smul, mul_comm lam, mul_assoc, mul_inv_cancel₀ hlam, mul_one]
  refine ⟨?_, ?_⟩
  · rw [jMapP_apply, map_sum]
    exact Finset.sum_eq_zero fun s _ => hl s
  · rw [jMapP_apply, map_sum, Fintype.sum_sum_type]
    simp only [hr]
    have hj : ∀ j : ι, rightPart P (liftVec P lam u v (Sum.inr j) •
        jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inr j)) =
        (u j - v j) • jVecP M₂ h P x j := by
      intro j
      rw [map_smul, (jVecP_modelSum_inr h₁ h₂ j x).2]
      rfl
    simp only [hj]
    have hpoly : ∑ i : NonPoly P, u i.1 • (jVecP M₁ h P x i.1 - jVecP M₂ h P x i.1) =
        ∑ k, u k • (jVecP M₁ h P x k - jVecP M₂ h P x k) := by
      set F : ι → ι → ℝ := fun k => u k • (jVecP M₁ h P x k - jVecP M₂ h P x k) with hF
      have e1 : ∑ i : NonPoly P, F i.1 =
          ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range P.emb), F k :=
        (Finset.sum_subtype (Finset.univ.filter fun k => k ∉ Set.range P.emb)
          (fun k => by simp) F).symm
      rw [e1]
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra hkr
      exact hk (by
        simp only [hF]
        rw [jVecP_eq_of_mem_range h₁ h₂ x hkr, sub_self, smul_zero])
    rw [hpoly, jMapP_apply, jMapP_apply]
    simp only [smul_sub, sub_smul, Finset.sum_sub_distrib]
    abel

end TwoModel

end RegularityStructures

end
