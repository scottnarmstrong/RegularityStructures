/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.PiGamma
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The generic model extension by abstract integration

`Model.intExtend` is the model `(Π', Γ')` on `𝒯'` built from a model `M` on `𝒯` realising the kernel
`K` (profile `h`) for `I` on `V` [Hai14, Theorem 5.14, Remark 5.10, (5.17)]:

* `Π'_x w = Π_x (restrictOld w) + ∑_{d ∈ D} w(new d) R_x d`, `R_x d = realRegP M h x d`;
* `Γ'_{xy} (liftOld v) = liftOld (Γ_{xy} v)`,
  `Γ'_{xy} e_{new d} = 𝓘 (liftOld Γ_{xy} e_d) + liftOld (J(x) Γ_{xy} e_d − Γ_{xy} J(y) e_d)`.

The measurability fields of the planted symbols are the only input not derived from `IntExtHyp`:
`IntExtMeas M h D` is the joint measurability of `(x, z) ↦ (Q_t g_{x,d})(z)`, `d ∈ D`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Joint measurability of `(x, z) ↦ (Q_t g_{x,d})(z)` for the planted symbols `d ∈ D`. -/
def IntExtMeas (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (D : Finset ι) : Prop :=
  ∀ d ∈ D, ∀ t : ℝ, 0 < t → Measurable fun p : ParabolicSpace × ParabolicSpace =>
    realRegP M h p.1 d t p.2

theorem IntExtMeas.measurable_diag {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ}
    {D : Finset ι} (hm : IntExtMeas M h D) {d : ι} (hd : d ∈ D) {t : ℝ} (ht : 0 < t) :
    Measurable fun x : ParabolicSpace => realRegP M h x d t x :=
  (hm d hd t ht).comp (f := fun x : ParabolicSpace => (x, x))
    (measurable_id.prodMk measurable_id)

theorem IntExtMeas.measurable_apply {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ}
    {D : Finset ι} (hm : IntExtMeas M h D) {d : ι} (hd : d ∈ D) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) : Measurable (realRegP M h x d t) :=
  (hm d hd t ht).comp (f := fun z : ParabolicSpace => (x, z))
    (measurable_const.prodMk measurable_id)

namespace IntExtHyp

open IntExt

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']
  {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}

theorem coe_piExt_single_old (H : IntExtHyp M E h N γ V) (x : ParabolicSpace) (i : ι) :
    (H.piExt x (Pi.single (E.old i) 1) : ℝ → ParabolicSpace → ℝ) =
      (M.pi x (Pi.single i 1) : ℝ → ParabolicSpace → ℝ) := by
  rw [← E.liftOld_single, H.piExt_liftOld]

theorem coe_piExt_single_new (H : IntExtHyp M E h N γ V) (x : ParabolicSpace) {d : ι}
    (hd : d ∈ D) :
    (H.piExt x (Pi.single (E.new d) 1) : ℝ → ParabolicSpace → ℝ) = realRegP M h x d := by
  rw [H.piExt_single_new x hd, H.coe_regD_of_mem hd]

/-- **The extended model** `(Π', Γ')` on `𝒯'` [Hai14, Theorem 5.14]. -/
def intExtend (H : IntExtHyp M E h N γ V) (hmeas : IntExtMeas M h D) :
    Model 𝒯' parabolicSemigroup where
  pi := H.piExt
  gamma x y := ⟨H.gammaExtUnit x y, H.gammaExtUnit_mem x y⟩
  pi_gamma x y τ := H.piExt_gammaExtMap x y τ
  gamma_self x := Subtype.ext (Units.ext (H.gammaExtMap_self x))
  gamma_mul x y z := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul]
    exact H.gammaExtMap_comp x y z))
  measurable_diag j t ht := by
    rcases E.cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
    · simp only [H.coe_piExt_single_old]
      exact M.measurable_diag i ht
    · simp only [H.coe_piExt_single_new _ hd]
      exact hmeas.measurable_diag hd ht
  measurable_pi x j t ht := by
    rcases E.cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
    · rw [H.coe_piExt_single_old]
      exact M.measurable_pi x i ht
    · rw [H.coe_piExt_single_new _ hd]
      exact hmeas.measurable_apply hd ht x

end IntExtHyp

end RegularityStructures

end
