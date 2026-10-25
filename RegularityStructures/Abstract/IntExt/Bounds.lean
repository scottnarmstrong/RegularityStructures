/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.OldSymbols
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising

/-!
# Inherited bounds below the level of the planted symbols

The planted symbol `new d` has degree `deg d + 2`.  At a level `γ' ≤ deg d + 2` for all `d ∈ D`, the
only symbols of degree `< γ'` are old, and `Π'`, `Γ'` restricted to them are `Π`, `Γ`:

* `piBoundOn_intExtend`, `gammaBoundOn_intExtend`: `M'.PiBoundOn γ' C S` and
  `M'.GammaBoundOn γ' C S` from the same bounds of `M` (any set `S`);
* `growthModel_intExtend`: `M'.GrowthModel γ' ...` from `M.GrowthModel γ' ...` (same level);
* `isJointMeasurable_intExtend`: joint measurability transfers.
-/

public section

open Set

namespace RegularityStructures

namespace IntegrationExtension

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} (E : IntegrationExtension 𝒯 𝒯' P P' I D)

/-- Below the level `γ' ≤ deg d + 2` (`d ∈ D`), every symbol of `𝒯'` is old. -/
theorem exists_old_of_deg_lt {γ' : ℝ} (hγ' : ∀ d ∈ D, γ' ≤ 𝒯.deg d + 2) {j : ι'}
    (hj : 𝒯'.deg j < γ') : ∃ i, j = E.old i := by
  rcases E.cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
  · exact ⟨i, rfl⟩
  · rw [E.deg_new d hd] at hj
    exact absurd hj (not_lt.2 (hγ' d hd))

end IntegrationExtension

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V) (hmeas : IntExtMeas M h D) {γ' : ℝ}

theorem growthModel_intExtend (hγ' : ∀ d ∈ D, γ' ≤ 𝒯.deg d + 2) {C C' p q : ℝ}
    {ρP' ρG' : ParabolicSpace → ℝ} (G : M.GrowthModel γ' C C' ρP' ρG' p q) :
    (H.intExtend hmeas).GrowthModel γ' C C' ρP' ρG' p q where
  pos := G.pos
  moderateP := G.moderateP
  moderateG := G.moderateG
  nonnegG := G.nonnegG
  piBound_nonneg := G.piBound_nonneg
  piBound j hj t ht x := by
    obtain ⟨i, rfl⟩ := E.exists_old_of_deg_lt hγ' hj
    rw [E.deg_old] at hj ⊢
    rw [H.intExtend_regPi_single_old hmeas]
    exact G.piBound i hj t ht x
  gammaBound i j hi hji x y := by
    obtain ⟨i0, rfl⟩ := E.exists_old_of_deg_lt hγ' hi
    obtain ⟨j0, rfl⟩ := E.exists_old_of_deg_lt hγ' (hji.trans hi)
    rw [E.deg_old] at hi hji ⊢
    rw [E.deg_old] at hji ⊢
    have e : (H.intExtend hmeas).gammaMap y x (Pi.single (E.old i0) 1) (E.old j0) =
        M.gammaMap y x (Pi.single i0 1) j0 := by
      rw [← E.liftOld_single, H.intExtend_gammaMap_liftOld hmeas, E.liftOld_apply_old]
    rw [e]
    exact G.gammaBound i0 j0 hi hji x y

/-- Joint measurability of `(x, z) ↦ (Q_t Π'_x e_j)(z)` for the extended model. -/
theorem isJointMeasurable_intExtend (hJ : M.IsJointMeasurable) :
    (H.intExtend hmeas).IsJointMeasurable := by
  intro j t ht
  rcases E.cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
  · have : (fun p : ParabolicSpace × ParabolicSpace =>
        (H.intExtend hmeas).regPi p.1 (Pi.single (E.old i) 1) t p.2) =
        fun p => M.regPi p.1 (Pi.single i 1) t p.2 := by
      funext p
      exact H.intExtend_regPi_single_old hmeas p.1 i t p.2
    rw [this]
    exact hJ i t ht
  · have : (fun p : ParabolicSpace × ParabolicSpace =>
        (H.intExtend hmeas).regPi p.1 (Pi.single (E.new d) 1) t p.2) =
        fun p => realRegP M h p.1 d t p.2 := by
      funext p
      exact H.intExtend_regPi_new hmeas hd p.1 t p.2
    rw [this]
    exact hmeas d hd t ht

end IntExtHyp

end RegularityStructures

end
