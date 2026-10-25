/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration
public import Mathlib.LinearAlgebra.Pi

/-!
# Extending a regularity structure by planted symbols `𝓘 d`

The interface of the generic model extension by abstract integration [Hai14, Theorem 5.14,
Remark 5.10, (5.17)]: a regularity structure `𝒯'` on an index type `ι'` that contains a copy of the
basis of `𝒯` (`old : ι → ι'`) and, for each symbol `d` of a finite set `D ⊂ ι` not integrated by `I`,
a new "planted" symbol `new d = 𝓘(d)` of degree `deg d + 2`.

* `IntExt.liftOld`, `IntExt.restrictOld`: the inclusion `T → T'` and the restriction `T' → T`;
* `IntExt.intExt old new D I = liftOld ∘ I ∘ restrictOld + ∑_{d ∈ D} (· (old d)) e_{new d}`: the
  abstract integration of the extended structure (`I` on the old symbols, `d ↦ 𝓘 d` on `D`);
* `IntegrationExtension`: the structural data, including the group sufficiency field of
  [Hai14, Theorem 5.14]: every linear map that restricts to an element of `G` on the old symbols
  and satisfies `g' e_{new d} − 𝓘 g' e_{old d} ∈ T̄ ∩ T_{<deg (new d)}` belongs to `G'`;
* `IntExt.mkVec a b = liftOld a + ∑_{d ∈ D} b_d e_{new d}`, the normal form of a vector of `T'`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExt

variable {ι ι' : Type*}

/-- The inclusion `T → T'`, `v ↦ (j ↦ v i if j = old i, else 0)`. -/
def liftOld (old : ι → ι') : (ι → ℝ) →ₗ[ℝ] (ι' → ℝ) :=
  Function.ExtendByZero.linearMap ℝ old

/-- The restriction `T' → T`, `w ↦ w ∘ old`. -/
def restrictOld (old : ι → ι') : (ι' → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.funLeft ℝ ℝ old

variable [Fintype ι] [DecidableEq ι] [DecidableEq ι']

/-- The abstract integration of the extended structure:
`liftOld ∘ I ∘ restrictOld + ∑_{d ∈ D} (w (old d)) e_{new d}`. -/
def intExt (old new : ι → ι') (D : Finset ι) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ) :=
  liftOld old ∘ₗ I ∘ₗ restrictOld old +
    ∑ d ∈ D, (LinearMap.proj (old d) : (ι' → ℝ) →ₗ[ℝ] ℝ).smulRight (Pi.single (new d) 1)

/-- The normal form `liftOld a + ∑_{d ∈ D} b_d e_{new d}` of a vector of `T'`. -/
def mkVec (old new : ι → ι') (D : Finset ι) (a b : ι → ℝ) : ι' → ℝ :=
  liftOld old a + ∑ d ∈ D, b d • (Pi.single (new d) 1 : ι' → ℝ)

end IntExt

open IntExt in
/-- The structural data of the extension of `𝒯` to `𝒯'` by the planted symbols `new d = 𝓘 d`,
`d ∈ D`, of degree `deg d + 2`, for an abstract integration `I` with `I e_d = 0` on `D`
[Hai14, Theorem 5.14].  `mem_group` is the group sufficiency field: the extended group `G'` of
[Hai14, Theorem 5.14] contains every `g'` which restricts to an element of `G` on the old symbols
and has `g' e_{new d} − 𝓘 g' e_{old d} ∈ T̄'`, of degree `< deg (new d)`, for `d ∈ D` (the degree
condition keeps `g'` graded unipotent). -/
structure IntegrationExtension {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (𝒯 : RegularityStructure ι) (𝒯' : RegularityStructure ι') {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (P' : PolynomialSector 𝒯' N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (D : Finset ι) where
  /-- The old symbols. -/
  old : ι → ι'
  /-- The planted symbols `𝓘 d`. -/
  new : ι → ι'
  old_injective : Function.Injective old
  new_injOn : Set.InjOn new (D : Set ι)
  old_ne_new : ∀ i, ∀ d ∈ D, old i ≠ new d
  cover : ∀ j, (∃ i, old i = j) ∨ ∃ d ∈ D, new d = j
  deg_old : ∀ i, 𝒯'.deg (old i) = 𝒯.deg i
  deg_new : ∀ d ∈ D, 𝒯'.deg (new d) = 𝒯.deg d + 2
  poly_emb : ∀ k, P'.emb k = old (P.emb k)
  I_D : ∀ d ∈ D, I (Pi.single d 1) = 0
  mem_group : ∀ g' : LinearMap.GeneralLinearGroup ℝ (ι' → ℝ),
    (∃ g ∈ 𝒯.group, ∀ v, (g' : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ)) (liftOld old v) =
      liftOld old ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) v)) →
    (∀ d ∈ D, (g' : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ)) (Pi.single (new d) 1) -
      intExt old new D I ((g' : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ)) (Pi.single (old d) 1)) ∈
        P'.subspace ⊓ lowerSubspace 𝒯'.deg (𝒯'.deg (new d))) →
    g' ∈ 𝒯'.group

end RegularityStructures

end

public section

namespace RegularityStructures

namespace IntExt

variable {ι ι' : Type*}

theorem liftOld_apply_old {old : ι → ι'} (hold : Function.Injective old) (v : ι → ℝ) (i : ι) :
    liftOld old v (old i) = v i := by
  simp [liftOld, hold.extend_apply]

theorem liftOld_apply_of_notMem {old : ι → ι'} (v : ι → ℝ) {j : ι'} (hj : ∀ i, old i ≠ j) :
    liftOld old v j = 0 := by
  have : j ∉ Set.range old := fun ⟨i, hi⟩ => hj i hi
  simp [liftOld, Function.extend_apply' _ _ _ (by simpa using hj)]

theorem restrictOld_apply (old : ι → ι') (w : ι' → ℝ) (i : ι) : restrictOld old w i = w (old i) :=
  rfl

theorem restrictOld_liftOld {old : ι → ι'} (hold : Function.Injective old) (v : ι → ℝ) :
    restrictOld old (liftOld old v) = v := by
  funext i
  rw [restrictOld_apply, liftOld_apply_old hold]

variable [DecidableEq ι] [DecidableEq ι']

theorem liftOld_single {old : ι → ι'} (hold : Function.Injective old) (i : ι) (c : ℝ) :
    liftOld old (Pi.single i c) = Pi.single (old i) c := by
  funext j
  by_cases hj : ∃ i', old i' = j
  · obtain ⟨i', rfl⟩ := hj
    rw [liftOld_apply_old hold]
    by_cases h : i' = i
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (hold e))]
  · push Not at hj
    rw [liftOld_apply_of_notMem _ hj, Pi.single_eq_of_ne]
    rintro rfl
    exact hj i rfl

omit [DecidableEq ι] in
theorem restrictOld_single_new {old new : ι → ι'} {D : Finset ι}
    (hne : ∀ i, ∀ d ∈ D, old i ≠ new d) {d : ι} (hd : d ∈ D) :
    restrictOld old (Pi.single (new d) 1 : ι' → ℝ) = 0 := by
  funext i
  rw [restrictOld_apply, Pi.single_eq_of_ne (hne i d hd)]
  rfl

omit [DecidableEq ι] in
theorem intExt_liftOld {old new : ι → ι'} {D : Finset ι} (hold : Function.Injective old)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    intExt old new D I (liftOld old u) =
      liftOld old (I u) + ∑ d ∈ D, u d • (Pi.single (new d) 1 : ι' → ℝ) := by
  simp [intExt, restrictOld_liftOld hold, liftOld_apply_old hold]

/-- `intExt` on the old basis vector `e_{old i}`: `𝓘 e_i`, plus the planted `e_{new i}` if
`i ∈ D`. -/
theorem intExt_single_old {old new : ι → ι'} {D : Finset ι} (hold : Function.Injective old)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (i : ι) :
    intExt old new D I (Pi.single (old i) 1) =
      liftOld old (I (Pi.single i 1)) + if i ∈ D then (Pi.single (new i) 1 : ι' → ℝ) else 0 := by
  rw [← liftOld_single hold, intExt_liftOld hold]
  congr 1
  by_cases hi : i ∈ D
  · rw [Finset.sum_eq_single_of_mem i hi]
    · simp [hi]
    · intro d' _ hne
      simp [hne.symm]
  · simp only [hi, ite_false]
    refine Finset.sum_eq_zero fun d' hd' => ?_
    have : d' ≠ i := fun h => hi (h ▸ hd')
    simp [this.symm]

omit [DecidableEq ι] in
theorem mkVec_apply_old {old new : ι → ι'} {D : Finset ι} (hold : Function.Injective old)
    (hne : ∀ i, ∀ d ∈ D, old i ≠ new d) (a b : ι → ℝ) (i : ι) :
    mkVec old new D a b (old i) = a i := by
  simp only [mkVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, liftOld_apply_old hold]
  rw [Finset.sum_eq_zero, add_zero]
  intro d hd
  rw [Pi.single_eq_of_ne (hne i d hd)]
  simp

omit [DecidableEq ι] in
theorem mkVec_apply_new {old new : ι → ι'} {D : Finset ι} (hne : ∀ i, ∀ d ∈ D, old i ≠ new d)
    (hnew : Set.InjOn new (D : Set ι)) (a b : ι → ℝ) {d : ι} (hd : d ∈ D) :
    mkVec old new D a b (new d) = b d := by
  simp only [mkVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [liftOld_apply_of_notMem _ (fun i => hne i d hd), zero_add,
    Finset.sum_eq_single_of_mem d hd]
  · simp
  · intro d' hd' hne'
    rw [Pi.single_eq_of_ne (fun h => hne' (hnew hd hd' h).symm)]
    simp

omit [DecidableEq ι] in
theorem mkVec_congr {old new : ι → ι'} {D : Finset ι} {a b b' : ι → ℝ}
    (h : ∀ d ∈ D, b d = b' d) : mkVec old new D a b = mkVec old new D a b' := by
  unfold mkVec
  rw [Finset.sum_congr rfl fun d hd => by rw [h d hd]]

omit [DecidableEq ι] in
theorem eq_mkVec {old new : ι → ι'} {D : Finset ι} (hold : Function.Injective old)
    (hne : ∀ i, ∀ d ∈ D, old i ≠ new d) (hnew : Set.InjOn new (D : Set ι))
    (hcover : ∀ j, (∃ i, old i = j) ∨ ∃ d ∈ D, new d = j) (w : ι' → ℝ) :
    w = mkVec old new D (restrictOld old w) (fun i => w (new i)) := by
  funext j
  rcases hcover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [mkVec_apply_old hold hne, restrictOld_apply]
  · rw [mkVec_apply_new hne hnew _ _ hd]

theorem liftOld_mem_subspace [Fintype ι] [Fintype ι'] {𝒯 : RegularityStructure ι}
    {𝒯' : RegularityStructure ι'} {N' : ℕ} {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'}
    {old : ι → ι'} (hold : Function.Injective old) (hemb : ∀ k, P'.emb k = old (P.emb k))
    {v : ι → ℝ} (hv : v ∈ P.subspace) : liftOld old v ∈ P'.subspace := by
  intro j hj
  by_cases h : ∃ i, old i = j
  · obtain ⟨i, rfl⟩ := h
    rw [liftOld_apply_old hold]
    refine hv i fun ⟨k, hk⟩ => hj ⟨k, ?_⟩
    rw [hemb, hk]
  · push Not at h
    exact liftOld_apply_of_notMem v h

end IntExt

namespace IntegrationExtension

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} (E : IntegrationExtension 𝒯 𝒯' P P' I D)

theorem liftOld_apply_old (v : ι → ℝ) (i : ι) : liftOld E.old v (E.old i) = v i :=
  IntExt.liftOld_apply_old E.old_injective v i

theorem liftOld_apply_new (v : ι → ℝ) {d : ι} (hd : d ∈ D) : liftOld E.old v (E.new d) = 0 :=
  liftOld_apply_of_notMem v fun i => E.old_ne_new i d hd

theorem liftOld_single (i : ι) (c : ℝ) :
    liftOld E.old (Pi.single i c) = Pi.single (E.old i) c :=
  IntExt.liftOld_single E.old_injective i c

theorem restrictOld_single_new {d : ι} (hd : d ∈ D) :
    restrictOld E.old (Pi.single (E.new d) 1 : ι' → ℝ) = 0 :=
  IntExt.restrictOld_single_new E.old_ne_new hd

theorem intExt_liftOld (u : ι → ℝ) :
    intExt E.old E.new D I (liftOld E.old u) =
      liftOld E.old (I u) + ∑ d ∈ D, u d • (Pi.single (E.new d) 1 : ι' → ℝ) :=
  IntExt.intExt_liftOld E.old_injective I u

theorem intExt_single_old (i : ι) :
    intExt E.old E.new D I (Pi.single (E.old i) 1) =
      liftOld E.old (I (Pi.single i 1)) + if i ∈ D then (Pi.single (E.new i) 1 : ι' → ℝ) else 0 :=
  IntExt.intExt_single_old E.old_injective I i

theorem mkVec_apply_old (a b : ι → ℝ) (i : ι) : mkVec E.old E.new D a b (E.old i) = a i :=
  IntExt.mkVec_apply_old E.old_injective E.old_ne_new a b i

theorem mkVec_apply_new (a b : ι → ℝ) {d : ι} (hd : d ∈ D) : mkVec E.old E.new D a b (E.new d) = b d :=
  IntExt.mkVec_apply_new E.old_ne_new E.new_injOn a b hd

theorem restrictOld_mkVec (a b : ι → ℝ) : restrictOld E.old (mkVec E.old E.new D a b) = a := by
  funext i
  rw [restrictOld_apply, E.mkVec_apply_old]

theorem eq_mkVec (w : ι' → ℝ) : w = mkVec E.old E.new D (restrictOld E.old w) (fun i => w (E.new i)) :=
  IntExt.eq_mkVec E.old_injective E.old_ne_new E.new_injOn E.cover w

theorem liftOld_mem_subspace {v : ι → ℝ} (hv : v ∈ P.subspace) : liftOld E.old v ∈ P'.subspace :=
  IntExt.liftOld_mem_subspace E.old_injective E.poly_emb hv

theorem single_new_eq_mkVec {d : ι} (hd : d ∈ D) :
    (Pi.single (E.new d) 1 : ι' → ℝ) = mkVec E.old E.new D 0 (Pi.single d 1) := by
  have h := E.eq_mkVec (Pi.single (E.new d) 1 : ι' → ℝ)
  rw [E.restrictOld_single_new hd] at h
  refine h.trans (mkVec_congr (fun d' hd' => ?_))
  by_cases e : d' = d
  · subst e; simp
  · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne]
    exact fun h' => e (E.new_injOn hd' hd h')

end IntegrationExtension

end RegularityStructures

end
