/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Integration
public import RegularityStructures.Abstract.Singular.TwoModel.Lift

/-!
# Side conditions of the integration data of the difference model

Hypotheses of the single-model Theorem 7.1 for `(𝒯⊕, P⊕, V⊕, I⊕)`:

* `sectorSum_basis`: `V⊕` is basis closed;
* `le_deg_of_single_mem_sectorSum`: `e_s ∈ V⊕ → ζ ≤ deg⊕ s` from the same for `V`;
* `intSum_apply_emb`: `I⊕` has no polynomial components on `V⊕`;
* `abs_intSum_single_le`: `|(I⊕ e_s)_t| ≤ C_I` if `|(I e_i)_j| ≤ C_I`;
* `liftVec_mem_sectorSum`: the lift `f⊕ = (λ Q f₁, f₁ - f₂)` takes values in `V⊕`.
-/

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

@[simp] theorem leftPart_single_inr (e : ι) : leftPart P (Pi.single (Sum.inr e) 1) = 0 := by
  funext i
  simp

@[simp] theorem rightPart_single_inr (e : ι) :
    rightPart P (Pi.single (Sum.inr e) 1) = Pi.single e 1 := by
  funext j
  simp [Pi.single_apply]

theorem sectorSum_basis (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    {a : NonPoly P ⊕ ι → ℝ} (ha : a ∈ sectorSum P V) (s : NonPoly P ⊕ ι) (hs : a s ≠ 0) :
    (Pi.single s 1 : NonPoly P ⊕ ι → ℝ) ∈ sectorSum P V := by
  rcases s with i | j
  · have h1 : extendNP P (leftPart P a) i.1 ≠ 0 := by
      rw [extendNP_apply_val]
      exact hs
    refine ⟨?_, ?_⟩
    · rw [single_inl, leftPart_pairVec, extendNP_single]
      exact hVb _ ha.1 _ h1
    · rw [single_inl, rightPart_pairVec]
      exact V.zero_mem
  · refine ⟨?_, ?_⟩
    · rw [single_inr, leftPart_pairVec, map_zero]
      exact V.zero_mem
    · rw [single_inr, rightPart_pairVec]
      exact hVb _ ha.2 _ hs

theorem single_mem_sectorSum_iff (s : NonPoly P ⊕ ι) :
    (Pi.single s 1 : NonPoly P ⊕ ι → ℝ) ∈ sectorSum P V ↔
      (match s with
        | Sum.inl i => (Pi.single i.1 1 : ι → ℝ) ∈ V
        | Sum.inr j => (Pi.single j 1 : ι → ℝ) ∈ V) := by
  rcases s with i | j
  · rw [mem_sectorSum, single_inl, leftPart_pairVec, rightPart_pairVec, extendNP_single]
    exact ⟨fun h => h.1, fun h => ⟨h, V.zero_mem⟩⟩
  · rw [mem_sectorSum, single_inr, leftPart_pairVec, rightPart_pairVec, map_zero]
    exact ⟨fun h => h.2, fun h => ⟨V.zero_mem, h⟩⟩

theorem le_deg_of_single_mem_sectorSum {ζ : ℝ} (hVα : ∀ i, (Pi.single i 1 : ι → ℝ) ∈ V → ζ ≤ 𝒯.deg i)
    (s : NonPoly P ⊕ ι) (hs : (Pi.single s 1 : NonPoly P ⊕ ι → ℝ) ∈ sectorSum P V) :
    ζ ≤ (structSumU P).deg s := by
  rcases s with i | j
  · exact hVα i.1 ((single_mem_sectorSum_iff P _).1 hs)
  · exact hVα j ((single_mem_sectorSum_iff P _).1 hs)

theorem intSum_apply_emb (hIp : ∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0)
    {a : NonPoly P ⊕ ι → ℝ} (ha : a ∈ sectorSum P V) (kk : PolyIndex N') :
    intSum P I a ((polySectorSum P).emb kk) = 0 :=
  (congrFun (rightPart_intSum P I a) (P.emb kk)).trans (hIp _ ha.2 kk)

theorem abs_intSum_single_le {CI : ℝ} (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI)
    (s t : NonPoly P ⊕ ι) : |intSum P I (Pi.single s 1) t| ≤ CI := by
  rcases s with i | i <;> rcases t with j | j
  · have e : intSum P I (Pi.single (Sum.inl i) 1) (Sum.inl j) = I (Pi.single i.1 1) j.1 := by
      show leftPart P (intSum P I _) j = _
      rw [leftPart_intSum, single_inl, leftPart_pairVec, extendNP_single]
      rfl
    rw [e]
    exact hCI i.1 j.1
  · have e : intSum P I (Pi.single (Sum.inl i) 1) (Sum.inr j) = 0 := by
      show rightPart P (intSum P I _) j = _
      rw [rightPart_intSum, single_inl, rightPart_pairVec, map_zero]
      rfl
    rw [e, abs_zero]
    exact (abs_nonneg _).trans (hCI i.1 j)
  · have e : intSum P I (Pi.single (Sum.inr i) 1) (Sum.inl j) = 0 := by
      show leftPart P (intSum P I _) j = _
      rw [leftPart_intSum, single_inr, leftPart_pairVec, map_zero, map_zero, map_zero]
      rfl
    rw [e, abs_zero]
    exact (abs_nonneg _).trans (hCI i j.1)
  · have e : intSum P I (Pi.single (Sum.inr i) 1) (Sum.inr j) = I (Pi.single i 1) j := by
      show rightPart P (intSum P I _) j = _
      rw [rightPart_intSum, single_inr, rightPart_pairVec]
    rw [e]
    exact hCI i j

theorem liftVec_mem_sectorSum (lam : ℝ)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) {u v : ι → ℝ} (hu : u ∈ V)
    (hv : v ∈ V) : liftVec P lam u v ∈ sectorSum P V := by
  refine ⟨?_, ?_⟩
  · change extendNP P (lam • restrictNP P u) ∈ V
    rw [map_smul]
    exact V.smul_mem _ (extendNP_restrictNP_mem P hVb hu)
  · exact V.sub_mem hu hv

end TwoModel

end RegularityStructures

end
