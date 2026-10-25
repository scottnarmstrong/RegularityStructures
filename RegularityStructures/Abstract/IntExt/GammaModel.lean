/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Pi
public import RegularityStructures.Abstract.IntExt.Degree
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The extended group elements `Γ'_{xy}`

`gammaExtMap H x y = E.gammaExt Γ_{xy} J(x) J(y)` with `J = jMapP M h P`
[Hai14, Theorem 5.14, proof]: on the old symbols `Γ'_{xy} (liftOld v) = liftOld (Γ_{xy} v)` and on the
planted symbols
`Γ'_{xy} e_{new d} = 𝓘 (liftOld (Γ_{xy} e_d)) + liftOld (J(x) Γ_{xy} e_d − Γ_{xy} J(y) e_d)`.
`gammaExtMap_self`, `gammaExtMap_comp` are the cocycle identities (`Γ_{xx} = 1`, telescoping, using
Lemma 5.16 for `W = V ∩ T_{<γ}` and the closure hypothesis for the `D`-components), and
`gammaExtUnit_mem` shows `Γ'_{xy} ∈ G'` through the group sufficiency field `IntegrationExtension.mem_group`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}

/-- The extended `Γ'_{xy}` as a linear map of `T'`. -/
def gammaExtMap (_H : IntExtHyp M E h N γ V) (x y : ParabolicSpace) :
    (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ) :=
  E.gammaExt (M.gammaMap x y) (jMapP M h P x) (jMapP M h P y)

end IntExtHyp

end RegularityStructures

end

public section

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

theorem projD_mem_lower (hD : ∀ d ∈ D, 𝒯.deg d < γ) (u : ι → ℝ) :
    projD D u ∈ lowerSubspace 𝒯.deg γ := by
  intro j hj
  refine projD_apply_of_notMem (fun hjD => ?_) u
  exact absurd (hD j hjD) (not_lt.2 hj)

include H in
theorem projD_mem_ext_lower (b : ι → ℝ) :
    projD D b ∈ extSector V D ∧ projD D b ∈ lowerSubspace 𝒯.deg γ :=
  ⟨Submodule.mem_sup_right (projD_mem_spanD b), projD_mem_lower H.deg_D b⟩

include H in
/-- `Γ_{xy}` maps `span D ∩ T_{<γ}` into `(V ⊔ span D) ∩ T_{<γ}`. -/
theorem gammaMap_mem_ext_lower (x y : ParabolicSpace) (b : ι → ℝ) :
    M.gammaMap x y (projD D b) ∈ extSector V D ∧
      M.gammaMap x y (projD D b) ∈ lowerSubspace 𝒯.deg γ := by
  obtain ⟨h1, h2⟩ := H.projD_mem_ext_lower b
  exact ⟨H.isSector_ext.invariant _ (M.gamma x y).2 _ h1,
    (M.isGradedUnipotent_gammaMap x y).map_lowerSubspace h2⟩

include H in
/-- The supplement property: `Γ_{xy} δ − ∑_{d'} (Γ_{xy} δ)_{d'} e_{d'} ∈ V ∩ T_{<γ}` for `δ ∈ span D`. -/
theorem gammaMap_supp (x y : ParabolicSpace) (b : ι → ℝ) :
    M.gammaMap x y (projD D b) - projD D (M.gammaMap x y (projD D b)) ∈
      V ⊓ lowerSubspace 𝒯.deg γ := by
  have e : M.gammaMap x y (projD D b) - projD D (M.gammaMap x y (projD D b)) =
      ∑ d ∈ D, b d • (M.gammaMap x y (Pi.single d 1) -
        projD D (M.gammaMap x y (Pi.single d 1))) := by
    rw [projD_apply D b]
    simp [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ ⟨?_, ?_⟩
  · exact H.closure' (M.gamma x y).2 hd
  · exact Submodule.sub_mem _ ((M.isGradedUnipotent_gammaMap x y).map_lowerSubspace
      (single_mem_lowerSubspace (H.deg_D d hd) 1)) (projD_mem_lower H.deg_D _)

theorem gammaExtMap_self (x : ParabolicSpace) : H.gammaExtMap x x = LinearMap.id := by
  unfold gammaExtMap
  rw [M.gammaMap_self]
  exact E.gammaExt_self _

theorem gammaExtMap_comp (x y z : ParabolicSpace) :
    H.gammaExtMap x y ∘ₗ H.gammaExtMap y z = H.gammaExtMap x z := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  refine E.gammaExt_comp _ _ _ _ _ _ (M.gammaMap_comp x y z) (V ⊓ lowerSubspace 𝒯.deg γ)
    ?_ ?_ (fun b => H.gammaMap_supp y z b) ?_
  · intro w hw
    exact ⟨H.sector.invariant _ (M.gamma x y).2 _ hw.1,
      (M.isGradedUnipotent_gammaMap x y).map_lowerSubspace hw.2⟩
  · intro w hw d hd
    exact H.coord_D hw.1 hd
  · intro w hw
    exact M.gammaMap_integral_add_jMap_of_mem_inP_growth H.profile H.realising H.integration
      H.sector H.coord (fun j hj => H.deg_gt j (Or.inl hj)) G
      (fun j hj => H.poly_deg j (Or.inl hj)) hw.1 hw.2 x y

theorem gammaExtMap_liftOld (x y : ParabolicSpace) (v : ι → ℝ) :
    H.gammaExtMap x y (liftOld E.old v) = liftOld E.old (M.gammaMap x y v) :=
  E.gammaExt_liftOld _ _ _ v

end IntExtHyp

end RegularityStructures

end

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

/-- `Γ'_{xy}` as an element of `GL(T')`, with inverse `Γ'_{yx}`. -/
def gammaExtUnit (x y : ParabolicSpace) : LinearMap.GeneralLinearGroup ℝ (ι' → ℝ) where
  val := H.gammaExtMap x y
  inv := H.gammaExtMap y x
  val_inv := by
    rw [Module.End.mul_eq_comp, H.gammaExtMap_comp, H.gammaExtMap_self]
    rfl
  inv_val := by
    rw [Module.End.mul_eq_comp, H.gammaExtMap_comp, H.gammaExtMap_self]
    rfl

end IntExtHyp

end RegularityStructures

end

public section

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

theorem gammaExtUnit_mem (x y : ParabolicSpace) : H.gammaExtUnit x y ∈ 𝒯'.group := by
  refine E.mem_group _ ⟨(M.gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)),
    (M.gamma x y).2, fun v => H.gammaExtMap_liftOld x y v⟩ fun d hd => ?_
  have h1 : (H.gammaExtUnit x y : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ)) (Pi.single (E.old d) 1) =
      liftOld E.old (M.gammaMap x y (Pi.single d 1)) := by
    rw [← E.liftOld_single]
    exact H.gammaExtMap_liftOld x y _
  have h2 : (H.gammaExtUnit x y : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ)) (Pi.single (E.new d) 1) =
      intExt E.old E.new D I (liftOld E.old (M.gammaMap x y (Pi.single d 1))) +
        liftOld E.old (jMapP M h P x (M.gammaMap x y (Pi.single d 1)) -
          M.gammaMap x y (jMapP M h P y (Pi.single d 1))) :=
    E.gammaExt_single_new _ _ _ hd
  rw [h2, h1, add_sub_cancel_left]
  refine ⟨E.liftOld_mem_subspace (Submodule.sub_mem _ (jMapP_mem_subspace M h P x _) ?_), ?_⟩
  · exact P.invariant _ (M.gamma x y).2 _ (jMapP_mem_subspace M h P y _)
  · rw [E.deg_new d hd]
    refine IntExt.liftOld_mem_lowerSubspace E.old_injective E.deg_old (Submodule.sub_mem _
      (jMapP_mem_lowerSubspace_of_le M h P x fun j hj => M.gammaMap_single_ne_zero_deg_le x y d j hj) ?_)
    refine (M.isGradedUnipotent_gammaMap x y).map_lowerSubspace ?_
    refine jMapP_mem_lowerSubspace_of_le M h P y fun j hj => ?_
    by_cases e : j = d
    · rw [e]
    · simp [e] at hj

end IntExtHyp

end RegularityStructures

end
