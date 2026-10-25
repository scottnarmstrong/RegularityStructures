/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Germ
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocalOrder
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Abstract.Profile.Realising

/-!
# `Π_x (I + J(x)) a + ∑_{d ∈ D} a_d R_x d = Q (K ∗ Π_x a)`

For `a ∈ (V ⊔ span D) ∩ T_{<γ}` and `R_x d = realRegP M h x d`:
  `Q_t Π_x (I a + J(x) a) + ∑_{d ∈ D} a_d (Q_t g_{x,d}) = Q_t (K ∗ Π_x a)`   (`regPi_ext_identity`).
For `a = e_j ∈ V` this is the realising property plus [Hai14, Remark 5.10]
(`regPi_integral_add_jMap_inP_growth`); for `a = e_d`, `d ∈ D`, it is `regPi_jMapP_add_realRegP`
(with `I e_d = 0`); the general case is by linearity (`kConv_finset_sum_growthP`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

include H in
/-- The identity on a basis vector `e_j` of `V ⊔ span D`, `deg j < γ`. -/
theorem regPi_ext_single {j : ι} (hj : (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D) (hjγ : 𝒯.deg j < γ)
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (I (Pi.single j 1) + jMapP M h P x (Pi.single j 1)) t z +
        (if j ∈ D then realRegP M h x j t z else 0) =
      parabolicSemigroup.apply t (kConvP h (fun t w => M.regPi x (Pi.single j 1) t w)) z := by
  by_cases hjD : j ∈ D
  · simp only [hjD, ↓reduceIte]
    rw [E.I_D j hjD, zero_add]
    exact H.regPi_jMapP_add_realRegP hj hjγ x ht z
  · simp only [hjD, ↓reduceIte, add_zero]
    obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
    have hjV : (Pi.single j 1 : ι → ℝ) ∈ V := hj.resolve_right hjD
    exact Model.regPi_integral_add_jMap_inP_growth H.profile H.realising H.sector H.coord
      (fun j hj => H.deg_gt j (Or.inl hj)) G hjγ hjV
      (H.poly_deg j hj hjγ) x ht z

include H in
/-- `Π_x (I + J(x)) a + ∑_{d ∈ D} a_d R_x d = Q (K ∗ Π_x a)` for `a ∈ (V ⊔ span D) ∩ T_{<γ}`. -/
theorem regPi_ext_identity {a : ι → ℝ} (ha : a ∈ extSector V D)
    (hal : a ∈ lowerSubspace 𝒯.deg γ) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t)
    (z : ParabolicSpace) :
    M.regPi x (I a + jMapP M h P x a) t z + ∑ d ∈ D, a d * realRegP M h x d t z =
      parabolicSemigroup.apply t (kConvP h (fun t w => M.regPi x a t w)) z := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  set S : Finset ι := 𝒯.sectorBelow (extSector V D) γ with hS
  have hmem : ∀ j ∈ S, (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D := fun j hj =>
    (single_mem_extSector_iff H.coord).1 ((𝒯.mem_sectorBelow _).1 hj).1
  have hKR : ∀ j ∈ S, KRegularG (fun t w => M.regPi x (Pi.single j 1) t w) x := fun j hj =>
    G.kRegularG_regPi_single H.isSector_ext H.coord_ext H.deg_gt_ext
      ((𝒯.mem_sectorBelow _).1 hj).1 ((𝒯.mem_sectorBelow _).1 hj).2 x
  have hDS : D ⊆ S := fun d hd =>
    (𝒯.mem_sectorBelow _).2 ⟨H.single_mem_ext_of_mem_D hd, H.deg_D d hd⟩
  have hasum : a = ∑ j ∈ S, a j • (Pi.single j 1 : ι → ℝ) := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, mul_one]
    · intro j _ hj
      simp [hj.symm]
    · intro hl
      by_cases h0 : a l = 0
      · simp [h0]
      · exact absurd ((𝒯.mem_sectorBelow _).2 ⟨H.coord_ext a ha l h0, by
          by_contra hlt
          exact h0 (hal l (not_lt.1 hlt))⟩) hl
  have hvec : I a + jMapP M h P x a =
      ∑ j ∈ S, a j • (I (Pi.single j 1) + jMapP M h P x (Pi.single j 1)) := by
    conv_lhs => rw [hasum]
    simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib]
  have hDsum : ∑ d ∈ D, a d * realRegP M h x d t z =
      ∑ j ∈ S, a j * (if j ∈ D then realRegP M h x j t z else 0) := by
    rw [← Finset.sum_subset hDS (fun j _ hj => by simp [hj])]
    exact Finset.sum_congr rfl fun d hd => by simp [hd]
  have hk : kConvP h (fun t w => M.regPi x a t w) =
      fun w => ∑ j ∈ S, a j * kConvP h (fun t w => M.regPi x (Pi.single j 1) t w) w := by
    funext w
    have hfam : (fun t w => M.regPi x a t w) =
        fun t w => ∑ j ∈ S, a j * M.regPi x (Pi.single j 1) t w := by
      funext t' w'
      exact M.regPi_eq_sum_sectorBelow H.coord_ext ha hal x t' w'
    rw [hfam]
    exact kConv_finset_sum_growthP S (fun j t w => M.regPi x (Pi.single j 1) t w) a hKR
      H.profile w
  rw [hvec, Model.regPi_finsetSum_smul, hDsum, hk,
    PolyBounded.apply_finsetSum S a _ (fun j hj => (hKR j hj).polyBounded_kConv_growthP H.profile)
      ht z, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_add, H.regPi_ext_single (hmem j hj) ((𝒯.mem_sectorBelow _).1 hj).2 x ht z]

end IntExtHyp

end RegularityStructures

end
