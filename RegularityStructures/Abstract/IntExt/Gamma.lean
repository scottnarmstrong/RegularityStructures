/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Basic

/-!
# The extended structure-group maps `Γ'_{xy}`, algebraically

For linear maps `G = Γ_{xy}`, `Jx = J(x)`, `Jy = J(y)` of `T`, the linear map `Γ'` of `T'` with
`Γ' (liftOld v) = liftOld (G v)` and
`Γ' e_{new d} = 𝓘 (liftOld (G e_d)) + liftOld (Jx G e_d − G Jy e_d)`
[Hai14, Theorem 5.14, proof] is `gammaExt`.  In the normal form `mkVec a b = liftOld a + ∑_d b_d e_{new d}`
with `δ = ∑_{d ∈ D} b_d e_d`:

  `Γ' (mkVec a b) = mkVec (G a + (𝓘 + Jx) G δ − G Jy δ) (G δ)`      (`gammaExt_mkVec`).

This is purely algebraic.  The cocycle identity (`gammaExt_comp`) holds provided there is a subspace
`W` (`= V ∩ T_{<γ}`) that is `G`-invariant, has no `D`-coordinates, supplements the span of `D`
in `G e_d` (`G e_d − ∑_{d' ∈ D} (G e_d)_{d'} e_{d'} ∈ W`) and satisfies Lemma 5.16 for `(I, J)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace IntExt

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']

/-- `b ↦ ∑_{d ∈ D} b_d e_d`: the coordinate projection of `T` onto `span {e_d : d ∈ D}`. -/
def projD (D : Finset ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ∑ d ∈ D, (LinearMap.proj d : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (Pi.single d 1)

/-- The linear form of `mkVec`: `(a, b) ↦ liftOld a + ∑_{d ∈ D} b_d e_{new d}`. -/
def mkL (old new : ι → ι') (D : Finset ι) : ((ι → ℝ) × (ι → ℝ)) →ₗ[ℝ] (ι' → ℝ) :=
  (liftOld old).coprod
    (∑ d ∈ D, (LinearMap.proj d : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (Pi.single (new d) 1))

end IntExt

namespace IntegrationExtension

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} (E : IntegrationExtension 𝒯 𝒯' P P' I D)

/-- The coordinates `(w (new d))_d` as the vector `∑_{d ∈ D} w(new d) e_d` of `T`. -/
def deltaD : (ι' → ℝ) →ₗ[ℝ] (ι → ℝ) := projD D ∘ₗ LinearMap.funLeft ℝ ℝ E.new

/-- The extended group map `Γ'` for `G = Γ_{xy}`, `Jx = J(x)`, `Jy = J(y)`. -/
def gammaExt (G Jx Jy : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (ι' → ℝ) →ₗ[ℝ] (ι' → ℝ) :=
  mkL E.old E.new D ∘ₗ
    ((G ∘ₗ restrictOld E.old + ((I + Jx) ∘ₗ G - G ∘ₗ Jy) ∘ₗ E.deltaD).prod (G ∘ₗ E.deltaD))

end IntegrationExtension

end RegularityStructures

end

public section

namespace RegularityStructures

namespace IntExt

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']

theorem projD_apply (D : Finset ι) (b : ι → ℝ) :
    projD D b = ∑ d ∈ D, b d • (Pi.single d 1 : ι → ℝ) := by
  simp [projD]

omit [DecidableEq ι'] in
theorem projD_apply_of_mem {D : Finset ι} {d : ι} (hd : d ∈ D) (b : ι → ℝ) : projD D b d = b d := by
  rw [projD_apply, Finset.sum_apply, Finset.sum_eq_single_of_mem d hd]
  · simp
  · intro d' _ hne
    simp [hne.symm]

theorem projD_apply_of_notMem {D : Finset ι} {d : ι} (hd : d ∉ D) (b : ι → ℝ) :
    projD D b d = 0 := by
  rw [projD_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun d' hd' => ?_
  have : d' ≠ d := fun h => hd (h ▸ hd')
  simp [this.symm]

theorem projD_congr {D : Finset ι} {b b' : ι → ℝ} (h : ∀ d ∈ D, b d = b' d) :
    projD D b = projD D b' := by
  rw [projD_apply, projD_apply]
  exact Finset.sum_congr rfl fun d hd => by rw [h d hd]

theorem map_projD {D : Finset ι} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hI : ∀ d ∈ D, I (Pi.single d 1) = 0)
    (b : ι → ℝ) : I (projD D b) = 0 := by
  rw [projD_apply, map_sum]
  exact Finset.sum_eq_zero fun d hd => by rw [map_smul, hI d hd, smul_zero]

omit [DecidableEq ι] in
theorem mkL_apply (old new : ι → ι') (D : Finset ι) (a b : ι → ℝ) :
    mkL old new D (a, b) = mkVec old new D a b := by
  simp [mkL, mkVec]

end IntExt

namespace IntegrationExtension

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} (E : IntegrationExtension 𝒯 𝒯' P P' I D)

theorem deltaD_mkVec (a b : ι → ℝ) : E.deltaD (mkVec E.old E.new D a b) = projD D b := by
  refine projD_congr fun d hd => ?_
  exact E.mkVec_apply_new a b hd

/-- The formula for `Γ'` in the normal form. -/
theorem gammaExt_mkVec (G Jx Jy : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a b : ι → ℝ) :
    E.gammaExt G Jx Jy (mkVec E.old E.new D a b) =
      mkVec E.old E.new D (G a + I (G (projD D b)) + Jx (G (projD D b)) - G (Jy (projD D b)))
        (G (projD D b)) := by
  show mkL E.old E.new D (_, _) = _
  rw [mkL_apply]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    E.restrictOld_mkVec, E.deltaD_mkVec]
  congr 1
  abel

theorem gammaExt_liftOld (G Jx Jy : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : ι → ℝ) :
    E.gammaExt G Jx Jy (liftOld E.old a) = liftOld E.old (G a) := by
  have h : liftOld E.old a = mkVec E.old E.new D a 0 := by simp [mkVec]
  rw [h, E.gammaExt_mkVec]
  simp [mkVec]

/-- `Γ' e_{new d} = 𝓘 (liftOld (G e_d)) + liftOld (Jx G e_d − G Jy e_d)`. -/
theorem gammaExt_single_new (G Jx Jy : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {d : ι} (hd : d ∈ D) :
    E.gammaExt G Jx Jy (Pi.single (E.new d) 1) =
      intExt E.old E.new D I (liftOld E.old (G (Pi.single d 1))) +
        liftOld E.old (Jx (G (Pi.single d 1)) - G (Jy (Pi.single d 1))) := by
  have hp : projD D (Pi.single d 1 : ι → ℝ) = Pi.single d 1 := by
    rw [projD_apply, Finset.sum_eq_single_of_mem d hd]
    · simp
    · intro d' _ hne
      simp [hne.symm]
  rw [E.single_new_eq_mkVec hd, E.gammaExt_mkVec, hp, E.intExt_liftOld]
  have ha : G 0 + I (G (Pi.single d 1)) + Jx (G (Pi.single d 1)) - G (Jy (Pi.single d 1)) =
      I (G (Pi.single d 1)) + (Jx (G (Pi.single d 1)) - G (Jy (Pi.single d 1))) := by
    rw [map_zero]; abel
  rw [ha]
  unfold mkVec
  rw [map_add]
  abel

end IntegrationExtension

end RegularityStructures

end
