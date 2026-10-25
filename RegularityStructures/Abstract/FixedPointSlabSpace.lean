/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointBounds
public import Mathlib.Analysis.Normed.Module.Basic
public import RegularityStructures.Abstract.Model

/-!
# `D^{γ,η}_P(V)` on a time slab as a normed space

[Hai14, §7.1, §7.3]: the fixed point of Theorem 7.8 lives in `D^{γ,η}_P` "on `(0, T)`", with the
norm `|||·|||_{γ,η;T}` of the singular modelled distributions restricted to the slab
`O_T = (−∞, T] × ℝ^{d−1}`. In the abstract setting the slab is a set `S ⊆ E`; only its points
off `P`, `S⁺ = S ∩ {ρ > 0}`, enter the bounds. To get a genuine (definite) norm, an element of the
slab space is a function **vanishing off `S⁺`** (a function on `S⁺`, extended by zero):

`slabModelledDistributions M ρ V γ η S` is the space of measurable `f : E → T` with

* `f(x) ∈ V ∩ T_{<γ}` for `x ∈ S⁺` (`V` a subspace, e.g. a sector; `V = ⊤` for none);
* `f(x) = 0` for `x ∉ S⁺`;
* `M.SingularBoundOn ρ γ η C S f` for some `C` ([Hai14, Definition 6.2] on `S`).

`slabNorm M ρ γ η S f` is the best constant (`singularBoundOn_slabNorm`, `slabNorm_le`).
`SlabSpace M ρ V γ η S` is the same space as a type with the norm `‖u‖ = slabNorm (u.val)`
(`SlabSpace.norm_def`): a `NormedAddCommGroup` and a `NormedSpace ℝ`. It is a type synonym of the
subtype because the subtype of `E → T` already carries the topology of pointwise convergence.
Completeness is in `RegularityStructures.Abstract.FixedPointSlabComplete`.

Source: [Hai14] = arXiv:1303.5113v4, Definition 6.2, §7.1 (the norms `|||·|||_{γ,η;T}`).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The singular modelled distributions `D^{γ,η}_P(V)` on the slab `S`, as functions vanishing
off `S⁺ = S ∩ {ρ > 0}` [Hai14, Definition 6.2, §7.1]. -/
def slabModelledDistributions (M : Model 𝒯 K) (ρ : E → ℝ) (V : Submodule ℝ (ι → ℝ)) (γ η : ℝ) (S : Set E) :
    Submodule ℝ (E → ι → ℝ) where
  carrier := {f | Measurable f ∧ (∀ x ∈ S, 0 < ρ x → f x ∈ V ⊓ lowerSubspace 𝒯.deg γ) ∧
    (∀ x, ¬(x ∈ S ∧ 0 < ρ x) → f x = 0) ∧ ∃ C, M.SingularBoundOn ρ γ η C S f}
  add_mem' := by
    rintro f g ⟨hf, hfV, hf0, Cf, hCf⟩ ⟨hg, hgV, hg0, Cg, hCg⟩
    refine ⟨hf.add hg, fun x hx hρ => Submodule.add_mem _ (hfV x hx hρ) (hgV x hx hρ),
      fun x hx => ?_, Cf + Cg, hCf.add M hCg⟩
    simp [hf0 x hx, hg0 x hx]
  zero_mem' := ⟨measurable_const, fun _ _ _ => Submodule.zero_mem _, fun _ _ => rfl, 0,
    M.singularBoundOn_zero ρ γ η S⟩
  smul_mem' := by
    rintro c f ⟨hf, hfV, hf0, Cf, hCf⟩
    refine ⟨hf.const_smul c, fun x hx hρ => Submodule.smul_mem _ c (hfV x hx hρ),
      fun x hx => ?_, |c| * Cf, hCf.smul M c⟩
    simp [hf0 x hx]

/-- The norm `|||f|||_{γ,η;S}`: the best constant in `SingularBoundOn` (real-valued). -/
def slabNorm (M : Model 𝒯 K) (ρ : E → ℝ) (γ η : ℝ) (S : Set E) (f : E → ι → ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ M.SingularBoundOn ρ γ η C S f}

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

variable {ρ : E → ℝ} {γ η : ℝ} {S : Set E}

theorem slabNorm_nonneg (f : E → ι → ℝ) : 0 ≤ M.slabNorm ρ γ η S f :=
  Real.sInf_nonneg fun _ h => h.1

theorem slabNorm_le {f : E → ι → ℝ} {C : ℝ} (h : M.SingularBoundOn ρ γ η C S f) (hC : 0 ≤ C) :
    M.slabNorm ρ γ η S f ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, h⟩

/-- The norm is attained: `|||f|||_{γ,η;S} ≤ slabNorm f` whenever some bound holds. -/
theorem singularBoundOn_slabNorm {f : E → ι → ℝ} (hf : ∃ C, M.SingularBoundOn ρ γ η C S f) :
    M.SingularBoundOn ρ γ η (M.slabNorm ρ γ η S f) S f := by
  obtain ⟨C, hC⟩ := hf
  have hne : {C : ℝ | 0 ≤ C ∧ M.SingularBoundOn ρ γ η C S f}.Nonempty :=
    ⟨max C 0, le_max_right _ _, hC.mono M (le_max_left _ _)⟩
  refine SingularBoundOn.of_forall_lt M fun C' hC' => ?_
  obtain ⟨c, hc, hcC'⟩ := exists_lt_of_csInf_lt hne hC'
  exact hc.2.mono M hcC'.le

theorem slabNorm_le_iff {f : E → ι → ℝ} (hf : ∃ C, M.SingularBoundOn ρ γ η C S f) {C : ℝ}
    (hC : 0 ≤ C) : M.slabNorm ρ γ η S f ≤ C ↔ M.SingularBoundOn ρ γ η C S f :=
  ⟨fun h => (M.singularBoundOn_slabNorm hf).mono M h, fun h => M.slabNorm_le h hC⟩

end Model

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The Banach space `D^{γ,η}_P(V)` on the slab `S` with the norm `|||·|||_{γ,η;S}`. It is a type
synonym of the subtype `slabModelledDistributions M ρ V γ η S`: that subtype of `E → T` carries
the topology of pointwise convergence, which must not be confused with the norm topology. -/
def SlabSpace (M : Model 𝒯 K) (ρ : E → ℝ) (V : Submodule ℝ (ι → ℝ)) (γ η : ℝ) (S : Set E) :
    Type _ :=
  M.slabModelledDistributions ρ V γ η S

variable {M : Model 𝒯 K} {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

instance : AddCommGroup (M.SlabSpace ρ V γ η S) :=
  inferInstanceAs (AddCommGroup (M.slabModelledDistributions ρ V γ η S))

instance : Module ℝ (M.SlabSpace ρ V γ η S) :=
  inferInstanceAs (Module ℝ (M.slabModelledDistributions ρ V γ η S))

namespace SlabSpace

/-- The underlying function `E → T` of an element of the slab space. -/
def val (u : M.SlabSpace ρ V γ η S) : E → ι → ℝ :=
  (show M.slabModelledDistributions ρ V γ η S from u).1

/-- An element of the slab space from a function and a membership proof. -/
def mk (f : E → ι → ℝ) (hf : f ∈ M.slabModelledDistributions ρ V γ η S) :
    M.SlabSpace ρ V γ η S :=
  (⟨f, hf⟩ : M.slabModelledDistributions ρ V γ η S)

end SlabSpace

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

namespace SlabSpace

theorem val_mem (u : M.SlabSpace ρ V γ η S) : u.val ∈ M.slabModelledDistributions ρ V γ η S :=
  (show M.slabModelledDistributions ρ V γ η S from u).2

@[simp] theorem val_mk (f : E → ι → ℝ) (hf : f ∈ M.slabModelledDistributions ρ V γ η S) :
    (mk f hf).val = f :=
  rfl

@[ext] theorem ext {u v : M.SlabSpace ρ V γ η S} (h : u.val = v.val) : u = v :=
  Subtype.ext (p := fun f => f ∈ M.slabModelledDistributions ρ V γ η S) h

@[simp] theorem val_zero : (0 : M.SlabSpace ρ V γ η S).val = 0 :=
  rfl

@[simp] theorem val_add (u v : M.SlabSpace ρ V γ η S) : (u + v).val = u.val + v.val :=
  rfl

@[simp] theorem val_neg (u : M.SlabSpace ρ V γ η S) : (-u).val = -u.val :=
  rfl

@[simp] theorem val_sub (u v : M.SlabSpace ρ V γ η S) : (u - v).val = u.val - v.val :=
  rfl

@[simp] theorem val_smul (c : ℝ) (u : M.SlabSpace ρ V γ η S) : (c • u).val = c • u.val :=
  rfl

theorem measurable (u : M.SlabSpace ρ V γ η S) : Measurable u.val :=
  u.val_mem.1

theorem mem_inf (u : M.SlabSpace ρ V γ η S) {x : E} (hx : x ∈ S) (hρ : 0 < ρ x) :
    u.val x ∈ V ⊓ lowerSubspace 𝒯.deg γ :=
  u.val_mem.2.1 x hx hρ

theorem apply_eq_zero (u : M.SlabSpace ρ V γ η S) {x : E} (hx : ¬(x ∈ S ∧ 0 < ρ x)) :
    u.val x = 0 :=
  u.val_mem.2.2.1 x hx

theorem singularBoundOn (u : M.SlabSpace ρ V γ η S) :
    M.SingularBoundOn ρ γ η (M.slabNorm ρ γ η S u.val) S u.val :=
  M.singularBoundOn_slabNorm u.val_mem.2.2.2

theorem slabNorm_le_iff (u : M.SlabSpace ρ V γ η S) {C : ℝ} (hC : 0 ≤ C) :
    M.slabNorm ρ γ η S u.val ≤ C ↔ M.SingularBoundOn ρ γ η C S u.val :=
  M.slabNorm_le_iff u.val_mem.2.2.2 hC

/-- An element of the slab space with norm `0` vanishes. -/
theorem eq_zero_of_slabNorm_eq_zero (u : M.SlabSpace ρ V γ η S)
    (h : M.slabNorm ρ γ η S u.val = 0) : u = 0 := by
  have hb := u.singularBoundOn
  rw [h] at hb
  ext x i
  by_cases hx : x ∈ S ∧ 0 < ρ x
  · by_cases hi : 𝒯.deg i < γ
    · exact hb.apply_eq_zero M hx.1 hx.2 hi
    · exact (Submodule.mem_inf.1 (u.mem_inf hx.1 hx.2)).2 i (not_lt.1 hi)
  · simp [u.apply_eq_zero hx]

end SlabSpace

end Model

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

/-- `D^{γ,η}_P(V)` on the slab `S` is a normed group for `|||·|||_{γ,η;S}`. -/
instance : NormedAddCommGroup (M.SlabSpace ρ V γ η S) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun u => M.slabNorm ρ γ η S u.val
      map_zero' := le_antisymm (M.slabNorm_le (M.singularBoundOn_zero ρ γ η S) le_rfl)
        (M.slabNorm_nonneg _)
      add_le' := fun u v => M.slabNorm_le (u.singularBoundOn.add M v.singularBoundOn)
        (add_nonneg (M.slabNorm_nonneg _) (M.slabNorm_nonneg _))
      neg' := fun u => le_antisymm
        (M.slabNorm_le u.singularBoundOn.neg (M.slabNorm_nonneg _))
        (by
          have h := (-u).singularBoundOn.neg
          rw [SlabSpace.val_neg, neg_neg] at h
          exact M.slabNorm_le h (M.slabNorm_nonneg _))
      eq_zero_of_map_eq_zero' := fun u h => u.eq_zero_of_slabNorm_eq_zero h }

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

namespace SlabSpace

/-- The bound of `D^{γ,η}_P` on `S` with the norm as constant. -/
theorem singularBoundOn_norm (u : M.SlabSpace ρ V γ η S) :
    M.SingularBoundOn ρ γ η ‖u‖ S u.val :=
  u.singularBoundOn

/-- `‖u‖ ≤ C ↔ |||u|||_{γ,η;S} ≤ C`. -/
theorem norm_le_iff (u : M.SlabSpace ρ V γ η S) {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ M.SingularBoundOn ρ γ η C S u.val :=
  u.slabNorm_le_iff hC

theorem norm_le (u : M.SlabSpace ρ V γ η S) {C : ℝ} (hC : 0 ≤ C)
    (h : M.SingularBoundOn ρ γ η C S u.val) : ‖u‖ ≤ C :=
  (u.norm_le_iff hC).2 h

end SlabSpace

end Model

end RegularityStructures

end
