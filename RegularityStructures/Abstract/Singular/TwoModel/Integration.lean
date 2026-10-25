/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import RegularityStructures.Abstract.Integration

/-!
# The integration data of the difference model

For a sector `V` of `𝒯` (basis closed) and an abstract integration map `I` of order `2` on `V`,
the sum data are
* `intSum P I = I⊕ : (a, b) ↦ (Q I E₀ a, I b)`;
* `sectorSum P V = V⊕ = {(a, b) | E₀ a ∈ V ∧ b ∈ V}`.

We prove `𝒯⊕.IsSector V⊕` (`isSector_sectorSum`), basis closedness, the lower bound on the degrees
of basis vectors of `V⊕`, `IsAbstractIntegration P⊕ V⊕ I⊕ 2` (`isAbstractIntegration_intSum`,
using the commutation `I Γ - Γ I ∈ P.subspace` on generators and closure induction), `I⊕` has no
polynomial components on `V⊕`, and the entries of `I⊕` are bounded by those of `I`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N')

/-- The integration map `I⊕ (a, b) = (Q I E₀ a, I b)` of the difference model. -/
def intSum (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ) :=
  blockMap P (restrictNP P ∘ₗ I ∘ₗ extendNP P) 0 I

/-- The sector `V⊕ = {(a, b) | E₀ a ∈ V ∧ b ∈ V}` of the difference model. -/
def sectorSum (V : Submodule ℝ (ι → ℝ)) : Submodule ℝ (NonPoly P ⊕ ι → ℝ) where
  carrier := {v | extendNP P (leftPart P v) ∈ V ∧ rightPart P v ∈ V}
  add_mem' {v w} hv hw := by
    refine ⟨?_, ?_⟩
    · simpa using V.add_mem hv.1 hw.1
    · simpa using V.add_mem hv.2 hw.2
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c v hv := by
    refine ⟨?_, ?_⟩
    · simpa using V.smul_mem c hv.1
    · simpa using V.smul_mem c hv.2

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

@[simp] theorem leftPart_intSum (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ) :
    leftPart P (intSum P I v) = restrictNP P (I (extendNP P (leftPart P v))) := rfl

@[simp] theorem rightPart_intSum (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ) :
    rightPart P (intSum P I v) = I (rightPart P v) := by
  change (0 : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (leftPart P v) + I (rightPart P v) = _
  simp

@[simp] theorem leftPart_blockGen (g g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ℝ)
    (v : NonPoly P ⊕ ι → ℝ) :
    leftPart P (blockGen P g g' c v) = restrictNP P (g (extendNP P (leftPart P v))) := rfl

@[simp] theorem rightPart_blockGen (g g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ℝ)
    (v : NonPoly P ⊕ ι → ℝ) :
    rightPart P (blockGen P g g' c v) =
      c • (g (extendNP P (leftPart P v)) - g' (extendNP P (leftPart P v))) +
        g' (rightPart P v) := by
  funext j
  simp [blockGen]

theorem mem_sectorSum {V : Submodule ℝ (ι → ℝ)} {v : NonPoly P ⊕ ι → ℝ} :
    v ∈ sectorSum P V ↔ extendNP P (leftPart P v) ∈ V ∧ rightPart P v ∈ V := Iff.rfl

theorem mem_polySubspaceSum_iff {v : NonPoly P ⊕ ι → ℝ} :
    v ∈ polySubspaceSum P ↔ leftPart P v = 0 ∧ rightPart P v ∈ P.subspace := by
  constructor
  · intro hv
    exact ⟨funext fun i => hv (Sum.inl i) (by simp), fun j hj =>
      hv (Sum.inr j) (by
        rintro ⟨k, hk⟩
        exact hj ⟨k, Sum.inr_injective hk⟩)⟩
  · rintro ⟨hl, hr⟩ s hs
    rcases s with i | j
    · exact congrFun hl i
    · exact hr j fun ⟨k, hk⟩ => hs ⟨k, by simp [hk]⟩

/-- For `g` in the structure group, `Q g E₀ Q = Q g`. -/
theorem restrictNP_apply_extendNP_restrictNP {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)}
    (hg : g ∈ 𝒯.group) (w : ι → ℝ) :
    restrictNP P ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (extendNP P (restrictNP P w))) =
      restrictNP P ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) w) := by
  have h := restrictNP_eq_zero_of_mem_subspace P
    (fun j hj => P.invariant g hg _ (sub_extendNP_restrictNP_mem P w) j hj)
  rw [map_sub, map_sub] at h
  exact (sub_eq_zero.1 h).symm

/-- `(g - g') E₀ Q = g - g'` when `g, g'` agree on `P.subspace`. -/
theorem sub_apply_extendNP_restrictNP {g g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hagree : ∀ p ∈ P.subspace, g p = g' p) (w : ι → ℝ) :
    g (extendNP P (restrictNP P w)) - g' (extendNP P (restrictNP P w)) = g w - g' w := by
  have h := hagree _ (sub_extendNP_restrictNP_mem P w)
  rw [map_sub, map_sub] at h
  linear_combination (norm := module) (-1 : ℝ) • h

section Sector

variable (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
include hVb

/-- `E₀ Q a ∈ V` for `a ∈ V` (`V` is basis closed). -/
theorem extendNP_restrictNP_mem {a : ι → ℝ} (ha : a ∈ V) :
    extendNP P (restrictNP P a) ∈ V := by
  rw [eq_sum_single (extendNP P (restrictNP P a))]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : extendNP P (restrictNP P a) j = 0
  · simp [hj]
  · refine V.smul_mem _ (hVb a ha j ?_)
    intro h0
    by_cases hjr : j ∈ Set.range P.emb
    · exact hj (extendNP_apply_of_mem P _ hjr)
    · exact hj (by rw [extendNP_apply_of_notMem P _ hjr]; exact h0)

end Sector

section Units

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem coe_mul_apply (g h : LinearMap.GeneralLinearGroup ℝ W) (a : W) :
    ((g * h : LinearMap.GeneralLinearGroup ℝ W) : W →ₗ[ℝ] W) a =
      (g : W →ₗ[ℝ] W) ((h : W →ₗ[ℝ] W) a) := rfl

theorem coe_inv_apply_apply (g : LinearMap.GeneralLinearGroup ℝ W) (a : W) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ W) : W →ₗ[ℝ] W) ((g : W →ₗ[ℝ] W) a) = a := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem coe_apply_inv_apply (g : LinearMap.GeneralLinearGroup ℝ W) (a : W) :
    (g : W →ₗ[ℝ] W) (((g⁻¹ : LinearMap.GeneralLinearGroup ℝ W) : W →ₗ[ℝ] W) a) = a := by
  rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

end Units

section Sector

variable (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
include hV hVb

theorem blockGen_mem_sectorSum {g g' : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)}
    (hg : g ∈ 𝒯.group) (hg' : g' ∈ 𝒯.group) (c : ℝ) {a : NonPoly P ⊕ ι → ℝ}
    (ha : a ∈ sectorSum P V) :
    blockGen P (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) c a ∈ sectorSum P V := by
  refine ⟨?_, ?_⟩
  · rw [leftPart_blockGen]
    exact extendNP_restrictNP_mem P hVb (hV.invariant g hg _ ha.1)
  · rw [rightPart_blockGen]
    exact V.add_mem (V.smul_mem c (V.sub_mem (hV.invariant g hg _ ha.1)
      (hV.invariant g' hg' _ ha.1))) (hV.invariant g' hg' _ ha.2)

theorem groupSumU_le_stabilizerGroup_sectorSum :
    groupSumU P ≤ stabilizerGroup (sectorSum P V) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro u ⟨g, hg, g', hg', -, c, hu⟩
  refine mem_stabilizerGroup_of_forall_mem _ u fun v hv => ?_
  rw [hu]
  exact blockGen_mem_sectorSum P hV hVb hg hg' c hv

theorem isSector_sectorSum : (structSumU P).IsSector (sectorSum P V) where
  graded α a ha := by
    have e1 : extendNP P (leftPart P (homogeneousProj (structSumU P).deg α a)) =
        homogeneousProj 𝒯.deg α (extendNP P (leftPart P a)) := by
      funext k
      by_cases hk : k ∈ Set.range P.emb
      · simp [extendNP_apply_of_mem P _ hk, homogeneousProj_apply]
      · by_cases hd : 𝒯.deg k = α <;>
          simp [extendNP_apply_of_notMem P _ hk, homogeneousProj_apply, structSumU, hd]
    have e2 : rightPart P (homogeneousProj (structSumU P).deg α a) =
        homogeneousProj 𝒯.deg α (rightPart P a) := by
      funext j
      by_cases hd : 𝒯.deg j = α <;> simp [homogeneousProj_apply, structSumU, hd]
    exact ⟨by rw [e1]; exact hV.graded α _ ha.1, by rw [e2]; exact hV.graded α _ ha.2⟩
  invariant g hg a ha := (groupSumU_le_stabilizerGroup_sectorSum P hV hVb hg a ha).1

end Sector

section Comm

variable (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
  (hI : IsAbstractIntegration P V I 2)
include hV hVb hI

omit hV in
theorem map_extendNP_restrictNP {a : ι → ℝ} (ha : a ∈ V) :
    I (extendNP P (restrictNP P a)) = I a := by
  have h := hI.map_poly _ (V.sub_mem ha (extendNP_restrictNP_mem P hVb ha))
    (sub_extendNP_restrictNP_mem P a)
  rw [map_sub] at h
  exact (sub_eq_zero.1 h).symm

theorem comm_blockGen {g g' : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)}
    (hg : g ∈ 𝒯.group) (hg' : g' ∈ 𝒯.group)
    (hagree : ∀ p ∈ P.subspace, (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) p = (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) p)
    (c : ℝ) {a : NonPoly P ⊕ ι → ℝ} (ha : a ∈ sectorSum P V) :
    intSum P I (blockGen P (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) c a) -
      blockGen P (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) c (intSum P I a) ∈
        polySubspaceSum P := by
  rw [mem_polySubspaceSum_iff]
  set A := extendNP P (leftPart P a) with hA
  have hAV : A ∈ V := ha.1
  refine ⟨?_, ?_⟩
  · rw [map_sub, leftPart_intSum, leftPart_blockGen, leftPart_blockGen, leftPart_intSum]
    have e1 := map_extendNP_restrictNP P hVb hI (hV.invariant g hg A hAV)
    have e2 := restrictNP_apply_extendNP_restrictNP P hg
      (I (extendNP P (leftPart P a)))
    rw [← hA] at e2
    rw [e1, e2, ← map_sub]
    exact restrictNP_eq_zero_of_mem_subspace P (hI.comm g hg A hAV)
  · rw [map_sub, rightPart_intSum, rightPart_blockGen, rightPart_blockGen, rightPart_intSum,
      leftPart_intSum]
    have e3 := sub_apply_extendNP_restrictNP P hagree (I A)
    have e : I (c • ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) A - (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) A) +
          (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (rightPart P a)) -
        (c • ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (extendNP P (restrictNP P (I A))) -
          (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (extendNP P (restrictNP P (I A)))) +
          (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I (rightPart P a))) =
        c • ((I ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) A) - (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I A)) -
          (I ((g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) A) - (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I A))) +
        (I ((g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (rightPart P a)) -
          (g' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I (rightPart P a))) := by
      rw [e3]
      simp only [map_add, map_smul, map_sub]
      module
    rw [e]
    exact P.subspace.add_mem (P.subspace.smul_mem _ (P.subspace.sub_mem (hI.comm g hg A hAV)
      (hI.comm g' hg' A hAV))) (hI.comm g' hg' _ ha.2)

theorem comm_of_mem_groupSumU {u : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)}
    (hu : u ∈ groupSumU P) (a : NonPoly P ⊕ ι → ℝ) (ha : a ∈ sectorSum P V) :
    intSum P I ((u : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a) -
      (u : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) (intSum P I a) ∈ polySubspaceSum P := by
  induction hu using Subgroup.closure_induction generalizing a with
  | mem u hu =>
    obtain ⟨g, hg, g', hg', hagree, c, hu⟩ := hu
    rw [hu]
    exact comm_blockGen P hV hVb hI hg hg' hagree c ha
  | one => simp
  | mul g h hg hh ihg ihh =>
    have hha : (h : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a ∈ sectorSum P V :=
      (groupSumU_le_stabilizerGroup_sectorSum P hV hVb hh a ha).1
    have h1 := ihg _ hha
    have h2 := (groupSumU_le_stabilizerGroup P hg _ (ihh a ha)).1
    have e : intSum P I (((g * h : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
          (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a) -
        ((g * h : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
          (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) (intSum P I a) =
        (intSum P I ((g : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ))
            ((h : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a)) -
          (g : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ))
            (intSum P I ((h : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a))) +
        (g : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ))
          (intSum P I ((h : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a) -
            (h : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) (intSum P I a)) := by
      rw [coe_mul_apply, coe_mul_apply, map_sub]
      abel
    rw [e]
    exact (polySubspaceSum P).add_mem h1 h2
  | inv g hg ihg =>
    have hb : ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
        (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a ∈ sectorSum P V :=
      (groupSumU_le_stabilizerGroup_sectorSum P hV hVb hg a ha).2
    have h1 := ihg _ hb
    rw [coe_apply_inv_apply] at h1
    have h2 := (groupSumU_le_stabilizerGroup P hg _ h1).2
    have e : intSum P I (((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
          (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a) -
        ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
          (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) (intSum P I a) =
        -(((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
          (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ))
          (intSum P I a - (g : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ))
            (intSum P I (((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ)) :
              (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ)) a)))) := by
      rw [map_sub, coe_inv_apply_apply, neg_sub]
    rw [e]
    exact (polySubspaceSum P).neg_mem h2

/-- `I⊕` is an abstract integration map of order `2` on `V⊕` for the polynomial sector `P⊕`. -/
theorem isAbstractIntegration_intSum :
    IsAbstractIntegration (polySectorSum P) (sectorSum P V) (intSum P I) 2 where
  pos := two_pos
  map_homogeneous α a ha hh := by
    have hL : extendNP P (leftPart P a) ∈ homogeneousSubspace 𝒯.deg α := by
      intro k hk
      by_cases hkr : k ∈ Set.range P.emb
      · exact extendNP_apply_of_mem P _ hkr
      · rw [extendNP_apply_of_notMem P _ hkr]
        exact hh (Sum.inl ⟨k, hkr⟩) hk
    have hR : rightPart P a ∈ homogeneousSubspace 𝒯.deg α := fun j hj => hh (Sum.inr j) hj
    have h1 := hI.map_homogeneous α _ ha.1 hL
    have h2 := hI.map_homogeneous α _ ha.2 hR
    intro s hs
    rcases s with i | j
    · exact h1 i.1 hs
    · exact (congrFun (rightPart_intSum P I a) j).trans (h2 j hs)
  map_poly a ha hp := by
    have hl : leftPart P a = 0 := ((mem_polySubspaceSum_iff P).1 hp).1
    have hr : rightPart P a ∈ P.subspace := ((mem_polySubspaceSum_iff P).1 hp).2
    funext s
    rcases s with i | j
    · have : leftPart P (intSum P I a) = 0 := by rw [leftPart_intSum, hl]; simp
      exact congrFun this i
    · have : rightPart P (intSum P I a) = 0 := by
        rw [rightPart_intSum]; exact hI.map_poly _ ha.2 hr
      exact congrFun this j
  comm u hu a ha := comm_of_mem_groupSumU P hV hVb hI hu a ha

end Comm

end TwoModel

end RegularityStructures

end
