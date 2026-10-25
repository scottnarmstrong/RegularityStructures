/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Model
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The extended model on the old and the planted symbols

* `intExtend_regPi_liftOld`: `Q_t Π'_x (liftOld v) = Q_t Π_x v`;
* `intExtend_gammaMap_liftOld`: `Γ'_{xy} (liftOld v) = liftOld (Γ_{xy} v)`;
* `intExtend_regPi_new`: `Q_t Π'_x e_{new d} = realRegP M h x d t`;
* `isPolyCompatible_intExtend`: `M'` is compatible with the polynomials `P'`;
* `realGermP_intExtend_old`, `realRegP_intExtend_old`: the germ of an old symbol is unchanged;
* `isRealisingP_intExtend`: `M'` realises the kernel `K` (profile `h`) for the integration
  `𝓘 = intExt old new D I` on the sector `liftedSector` spanned by `e_{old i}`, `e_i ∈ V` or `i ∈ D`,
  at level `γ`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq ι']

/-- The sector of `T'` spanned by `e_{old i}`, `i ∈ V ⊔ span D`. -/
def liftedSector (old : ι → ι') (V : Submodule ℝ (ι → ℝ)) (D : Finset ι) :
    Submodule ℝ (ι' → ℝ) :=
  (extSector V D).map (liftOld old)

end IntExt

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
  (H : IntExtHyp M E h N γ V) (hmeas : IntExtMeas M h D)

theorem intExtend_regPi_liftOld (x : ParabolicSpace) (v : ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    (H.intExtend hmeas).regPi x (liftOld E.old v) t z = M.regPi x v t z := by
  show (H.piExt x (liftOld E.old v) : ℝ → ParabolicSpace → ℝ) t z = _
  rw [H.piExt_liftOld]
  rfl

theorem intExtend_regPi_single_old (x : ParabolicSpace) (i : ι) (t : ℝ) (z : ParabolicSpace) :
    (H.intExtend hmeas).regPi x (Pi.single (E.old i) 1) t z = M.regPi x (Pi.single i 1) t z := by
  rw [← E.liftOld_single, H.intExtend_regPi_liftOld hmeas]

theorem intExtend_gammaMap_liftOld (x y : ParabolicSpace) (v : ι → ℝ) :
    (H.intExtend hmeas).gammaMap x y (liftOld E.old v) = liftOld E.old (M.gammaMap x y v) :=
  H.gammaExtMap_liftOld x y v

theorem intExtend_regPi_new {d : ι} (hd : d ∈ D) (x : ParabolicSpace) (t : ℝ)
    (z : ParabolicSpace) :
    (H.intExtend hmeas).regPi x (Pi.single (E.new d) 1) t z = realRegP M h x d t z := by
  show (H.piExt x (Pi.single (E.new d) 1) : ℝ → ParabolicSpace → ℝ) t z = _
  rw [H.piExt_single_new x hd, H.coe_regD_of_mem hd]

include H in
theorem isPolyCompatible_intExtend : (H.intExtend hmeas).IsPolyCompatible P' := by
  intro x k t z
  rw [E.poly_emb, H.intExtend_regPi_single_old hmeas]
  exact H.realising.poly x k t z

theorem realGermP_intExtend_old (x : ParabolicSpace) (i : ι) (y : ParabolicSpace) :
    realGermP (H.intExtend hmeas) h x (E.old i) y = realGermP M h x i y := by
  have hf : (fun t z => (H.intExtend hmeas).regPi x (Pi.single (E.old i) 1) t z) =
      fun t z => M.regPi x (Pi.single i 1) t z := by
    funext t z
    exact H.intExtend_regPi_single_old hmeas x i t z
  unfold realGermP
  rw [hf, E.deg_old]

theorem realRegP_intExtend_old (x : ParabolicSpace) (i : ι) (t : ℝ) (z : ParabolicSpace) :
    realRegP (H.intExtend hmeas) h x (E.old i) t z = realRegP M h x i t z := by
  have hg : realGermP (H.intExtend hmeas) h x (E.old i) = realGermP M h x i := by
    funext y
    exact H.realGermP_intExtend_old hmeas x i y
  unfold realRegP
  rw [hg]

include H in
theorem single_mem_liftedSector {j : ι'}
    (hj : (Pi.single j 1 : ι' → ℝ) ∈ liftedSector E.old V D) :
    ∃ i, j = E.old i ∧ ((Pi.single i 1 : ι → ℝ) ∈ V ∨ i ∈ D) := by
  obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 hj
  rcases E.cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
  · refine ⟨i, rfl, ?_⟩
    have h1 : a i = 1 := by
      have := congrFun e (E.old i)
      rwa [E.liftOld_apply_old, Pi.single_eq_same] at this
    exact (single_mem_extSector_iff H.coord).1 (H.coord_ext a ha i (by rw [h1]; exact one_ne_zero))
  · have := congrFun e (E.new d)
    rw [E.liftOld_apply_new _ hd, Pi.single_eq_same] at this
    exact absurd this.symm one_ne_zero

include H in
theorem isRealisingP_intExtend :
    (H.intExtend hmeas).IsRealisingP h γ P' (intExt E.old E.new D I)
      (liftedSector E.old V D) := by
  refine ⟨fun x j hjγ hjV t ht z => ?_, H.isPolyCompatible_intExtend hmeas⟩
  obtain ⟨i, rfl, hi⟩ := H.single_mem_liftedSector hjV
  rw [E.deg_old] at hjγ
  rw [E.intExt_single_old, Model.regPi_add, H.intExtend_regPi_liftOld hmeas,
    H.realRegP_intExtend_old hmeas]
  by_cases hiD : i ∈ D
  · simp only [hiD, ↓reduceIte]
    rw [E.I_D i hiD, H.intExtend_regPi_new hmeas hiD]
    simp [Model.regPi]
  · simp only [hiD, ↓reduceIte]
    rw [H.realising.realises x i hjγ (hi.resolve_right hiD) t ht z]
    simp [Model.regPi]

end IntExtHyp

end RegularityStructures

end
