/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Identity
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The extended `Π'`

`Π'_x w = Π_x (restrictOld w) + ∑_{d ∈ D} w(new d) R_x d`, where `R_x d = realRegP M h x d` is the
`Q`-family of the germ of `Π_x I e_d` [Hai14, Remark 5.10, (5.17)].  `IntExtHyp.piExt` is a linear
map `T' → 𝒟'` (`parabolicSemigroup.distributions`), with
`piExt_liftOld : Π'_x (liftOld v) = Π_x v` and `piExt_single_new : Π'_x e_{new d} = R_x d`.
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
  (H : IntExtHyp M E h N γ V)

/-- `R_x d = Q_t g_{x,d}` as a `Q`-distribution (zero off `D`). -/
def regD (x : ParabolicSpace) (d : ι) : parabolicSemigroup.distributions :=
  if hd : d ∈ D then ⟨realRegP M h x d, H.realRegP_mem_ext hd x⟩ else 0

/-- The extended `Π'_x : T' → 𝒟'`. -/
def piExt (x : ParabolicSpace) : (ι' → ℝ) →ₗ[ℝ] parabolicSemigroup.distributions :=
  M.pi x ∘ₗ restrictOld E.old +
    ∑ d ∈ D, (LinearMap.proj (E.new d) : (ι' → ℝ) →ₗ[ℝ] ℝ).smulRight (H.regD x d)

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

theorem coe_regD_of_mem {d : ι} (hd : d ∈ D) (x : ParabolicSpace) :
    (H.regD x d : ℝ → ParabolicSpace → ℝ) = realRegP M h x d := by
  simp [regD, hd]

theorem piExt_mkVec (x : ParabolicSpace) (a b : ι → ℝ) :
    H.piExt x (mkVec E.old E.new D a b) = M.pi x a + ∑ d ∈ D, b d • H.regD x d := by
  simp only [piExt, LinearMap.add_apply, LinearMap.comp_apply, E.restrictOld_mkVec,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_proj, Function.eval]
  congr 1
  exact Finset.sum_congr rfl fun d hd => by rw [E.mkVec_apply_new a b hd]

/-- `(Q_t Π'_x (mkVec a b))(z) = (Q_t Π_x a)(z) + ∑_d b_d (Q_t g_{x,d})(z)`. -/
theorem regPi_piExt_mkVec (x : ParabolicSpace) (a b : ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    (H.piExt x (mkVec E.old E.new D a b) : ℝ → ParabolicSpace → ℝ) t z =
      M.regPi x a t z + ∑ d ∈ D, b d * realRegP M h x d t z := by
  rw [H.piExt_mkVec]
  simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine congrArg₂ _ rfl (Finset.sum_congr rfl fun d hd => ?_)
  rw [H.coe_regD_of_mem hd]

theorem piExt_liftOld (x : ParabolicSpace) (v : ι → ℝ) :
    H.piExt x (liftOld E.old v) = M.pi x v := by
  have h0 : liftOld E.old v = mkVec E.old E.new D v 0 := by simp [mkVec]
  rw [h0, H.piExt_mkVec]
  simp

theorem piExt_single_new (x : ParabolicSpace) {d : ι} (hd : d ∈ D) :
    H.piExt x (Pi.single (E.new d) 1) = H.regD x d := by
  rw [E.single_new_eq_mkVec hd, H.piExt_mkVec, map_zero, zero_add,
    Finset.sum_eq_single_of_mem d hd]
  · simp
  · intro d' _ hne
    simp [hne.symm]

end IntExtHyp

end RegularityStructures

end
