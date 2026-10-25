/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Hyp
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Consequences of `IntExtHyp`: the enlarged sector `V₂ = V ⊔ span D`

Under `IntExtHyp` the subspace `V ⊔ span D` is a coordinate-closed sector (`isSector_ext`,
`coord_ext`) with basis vectors those of `V` and `D`, satisfying the degree conditions
(`deg_gt_ext`, `poly_deg_ext`) needed for the growth versions of the germ identity.  Also
`closure'`: `G e_d − ∑_{d'} (G e_d)_{d'} e_{d'} ∈ V`.
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
theorem projD_eq_zero_of_mem {v : ι → ℝ} (hv : v ∈ V) : projD D v = 0 :=
  projD_eq_zero_of_coord fun d hd => by
    by_contra h0
    exact H.notMem_D d hd (H.coord v hv d h0)

include H in
theorem coord_D {v : ι → ℝ} (hv : v ∈ V) {d : ι} (hd : d ∈ D) : v d = 0 := by
  by_contra h0
  exact H.notMem_D d hd (H.coord v hv d h0)

include H in
/-- `G e_d − ∑_{d'} (G e_d)_{d'} e_{d'} ∈ V` for `G` in the structure group. -/
theorem closure' {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)} (hg : g ∈ 𝒯.group) {d : ι}
    (hd : d ∈ D) :
    (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single d 1) -
      projD D ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single d 1)) ∈ V := by
  obtain ⟨s, hs, v, hv, e⟩ := Submodule.mem_sup.1 (H.closure g hg d hd)
  have hs' : s ∈ spanD D := span_le_spanD hs
  rw [← e, map_add, projD_eq_self hs', H.projD_eq_zero_of_mem hv, add_zero]
  simpa using hv

include H in
theorem closure_ext {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)} (hg : g ∈ 𝒯.group) {d : ι}
    (hd : d ∈ D) :
    (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single d 1) ∈ extSector V D := by
  obtain ⟨s, hs, v, hv, e⟩ := Submodule.mem_sup.1 (H.closure g hg d hd)
  rw [← e, add_comm]
  exact Submodule.add_mem_sup hv (span_le_spanD hs)

include H in
theorem isSector_ext : 𝒯.IsSector (extSector V D) :=
  extSector_isSector H.sector fun _ hg _ hd => H.closure_ext hg hd

include H in
theorem coord_ext : ∀ a ∈ extSector V D, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ extSector V D :=
  extSector_coord H.coord

include H in
theorem deg_gt_ext : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ extSector V D → 𝒯.deg j < γ →
    -2 < 𝒯.deg j := fun j hj => H.deg_gt j ((single_mem_extSector_iff H.coord).1 hj)

include H in
theorem poly_deg_ext : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ extSector V D → 𝒯.deg j < γ →
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N' :=
  fun j hj => H.poly_deg j ((single_mem_extSector_iff H.coord).1 hj)

include H in
theorem single_mem_ext_of_mem {j : ι} (hj : (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D) :
    (Pi.single j 1 : ι → ℝ) ∈ extSector V D := (single_mem_extSector_iff H.coord).2 hj

include H in
theorem single_mem_ext_of_mem_D {d : ι} (hd : d ∈ D) : (Pi.single d 1 : ι → ℝ) ∈ extSector V D :=
  H.single_mem_ext_of_mem (Or.inr hd)

end IntExtHyp

end RegularityStructures

end
