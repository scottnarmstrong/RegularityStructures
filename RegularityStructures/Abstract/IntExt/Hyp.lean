/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Cocycle
public import RegularityStructures.Abstract.Profile.Growth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Standing hypotheses of the model extension, and the enlarged sector `V ⊔ span D`

`IntExtHyp M E h N γ V` bundles the hypotheses under which the model `M` extends along the
`IntegrationExtension E` (Prop-valued): `M` realises the kernel with profile `h` for `I` on the sector
`V`, `I` is an abstract integration of order `2` on `V`, qualitative weighted bounds
(`Model.GrowthModel`), degrees `> -2` below `γ` on `V` and on `D`, the polynomial sector is large
enough (`poly_deg`), and the planted symbols `d ∈ D` are not in `V` and have `G e_d ∈ span D ⊔ V`
(`closure`, the closure hypothesis `hDV`).

The growth hypothesis is *qualitative*: it is used only for convergence of the shell series, the
germ identity and measurability, not for quantitative bounds.

The enlarged sector `V₂ = V ⊔ spanD D` is a coordinate-closed sector (`isSector_extSector`,
`extSector_coord`) whose basis vectors are those of `V` and of `D` (`single_mem_extSector_iff`); it
is the sector on which `Π_x e_j` is `KRegularG`.  The subspace `W = V ∩ T_{<γ}` carries Lemma 5.16
(`h516`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate subspace `{a : a_j = 0 for j ∉ D}`, i.e. `span {e_d : d ∈ D}`. -/
def spanD (D : Finset ι) : Submodule ℝ (ι → ℝ) where
  carrier := {a | ∀ j, j ∉ D → a j = 0}
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' _ _ := rfl
  smul_mem' c a ha j hj := by simp [ha j hj]

/-- The enlarged sector `V ⊔ span {e_d : d ∈ D}`. -/
def extSector (V : Submodule ℝ (ι → ℝ)) (D : Finset ι) : Submodule ℝ (ι → ℝ) := V ⊔ spanD D

end IntExt

open IntExt in
/-- The standing hypotheses of the model extension (see the module docstring). -/
structure IntExtHyp {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
    {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    {D : Finset ι} (M : Model 𝒯 parabolicSemigroup) (_E : IntegrationExtension 𝒯 𝒯' P P' I D)
    (h : ParabolicSpace → ℝ) (N : ℕ) (γ : ℝ) (V : Submodule ℝ (ι → ℝ)) : Prop where
  profile : ShellProfile h N
  realising : M.IsRealisingP h γ P I V
  integration : IsAbstractIntegration P V I 2
  sector : 𝒯.IsSector V
  coord : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V
  deg_gt : ∀ j, ((Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D) → 𝒯.deg j < γ → -2 < 𝒯.deg j
  growth : ∃ (C C' p q : ℝ) (ρP ρG : ParabolicSpace → ℝ), M.GrowthModel γ C C' ρP ρG p q
  poly_deg : ∀ j, ((Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D) → 𝒯.deg j < γ →
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N'
  deg_D : ∀ d ∈ D, 𝒯.deg d < γ
  notMem_D : ∀ d ∈ D, (Pi.single d 1 : ι → ℝ) ∉ V
  closure : ∀ g ∈ 𝒯.group, ∀ d ∈ D,
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single d 1) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : ι → ℝ)) '' (D : Set ι)) ⊔ V

end RegularityStructures

end

public section

namespace RegularityStructures

namespace IntExt

variable {ι : Type*} [DecidableEq ι] {D : Finset ι} {V : Submodule ℝ (ι → ℝ)}

theorem single_mem_spanD {d : ι} (hd : d ∈ D) (c : ℝ) : (Pi.single d c : ι → ℝ) ∈ spanD D := by
  intro j hj
  have : j ≠ d := fun h => hj (h ▸ hd)
  simp [this]

theorem span_le_spanD :
    Submodule.span ℝ ((fun d => (Pi.single d 1 : ι → ℝ)) '' (D : Set ι)) ≤ spanD D := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨d, hd, rfl⟩
  exact single_mem_spanD hd 1

theorem projD_eq_self {a : ι → ℝ} (ha : a ∈ spanD D) : projD D a = a := by
  funext j
  by_cases hj : j ∈ D
  · exact projD_apply_of_mem hj a
  · rw [projD_apply_of_notMem hj, ha j hj]

theorem projD_mem_spanD (a : ι → ℝ) : projD D a ∈ spanD D :=
  fun _ hj => projD_apply_of_notMem hj a

theorem projD_eq_zero_of_coord {v : ι → ℝ} (hv : ∀ d ∈ D, v d = 0) : projD D v = 0 := by
  funext j
  by_cases hj : j ∈ D
  · rw [projD_apply_of_mem hj, hv j hj]; rfl
  · rw [projD_apply_of_notMem hj]; rfl

/-- `e_j ∈ V ⊔ span D` iff `e_j ∈ V` or `j ∈ D`. -/
theorem single_mem_extSector_iff (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    {j : ι} : (Pi.single j 1 : ι → ℝ) ∈ extSector V D ↔ (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D := by
  constructor
  · intro h
    obtain ⟨v, hv, s, hs, e⟩ := Submodule.mem_sup.1 h
    by_cases hj : j ∈ D
    · exact Or.inr hj
    · refine Or.inl (hVb v hv j ?_)
      have := congrFun e j
      simp only [Pi.add_apply, Pi.single_eq_same, hs j hj, add_zero] at this
      rw [this]
      exact one_ne_zero
  · rintro (h | h)
    · exact Submodule.mem_sup_left h
    · exact Submodule.mem_sup_right (single_mem_spanD h 1)

theorem extSector_coord (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) :
    ∀ a ∈ extSector V D, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ extSector V D := by
  intro a ha j hj
  obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 ha
  by_cases hjD : j ∈ D
  · exact Submodule.mem_sup_right (single_mem_spanD hjD 1)
  · refine Submodule.mem_sup_left (hVb v hv j ?_)
    simpa [hs j hjD] using hj

theorem extSector_isSector [Fintype ι] {𝒯 : RegularityStructure ι} (hV : 𝒯.IsSector V)
    (hcl : ∀ g ∈ 𝒯.group, ∀ d ∈ D,
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single d 1) ∈
        extSector V D) : 𝒯.IsSector (extSector V D) where
  graded α a ha := by
    obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add]
    refine Submodule.add_mem_sup (hV.graded α v hv) ?_
    intro j hj
    rw [homogeneousProj_apply, hs j hj]
    simp
  invariant g hg a ha := by
    obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hV.invariant g hg v hv)) ?_
    have hs' : s = ∑ d ∈ D, s d • (Pi.single d 1 : ι → ℝ) := by
      rw [← projD_apply, projD_eq_self hs]
    rw [hs', map_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hcl g hg d hd)

end IntExt

end RegularityStructures

end
