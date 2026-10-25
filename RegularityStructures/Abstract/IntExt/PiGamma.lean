/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.GammaModel
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# `Π'_x Γ'_{xy} = Π'_y`

The pairing identity of the extended model [Hai14, Theorem 5.14, Remark 5.10].  In the normal form
`w = mkVec a b` (with `δ = ∑_d b_d e_d`):

  `Π'_x Γ'_{xy} w = Π_x Γ_{xy} a + Π_x (I + J(x)) Γ_{xy} δ − Π_x Γ_{xy} J(y) δ + ∑_d (Γ_{xy} δ)_d R_x d`,

and `Π_x (I + J(x)) Γ_{xy} δ + ∑_d (Γ_{xy} δ)_d R_x d = Q (K ∗ Π_x Γ_{xy} δ) = Q (K ∗ Π_y δ)`
(`regPi_ext_identity` at `x` on `Γ_{xy} δ`), while at `y` on `δ`:
`Π_y J(y) δ + ∑_d b_d R_y d = Q (K ∗ Π_y δ)`.
-/

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

theorem regPi_eq_zero_of_nonpos (x : ParabolicSpace) (τ : ι → ℝ) {t : ℝ} (ht : t ≤ 0)
    (z : ParabolicSpace) : M.regPi x τ t z = 0 :=
  congrFun ((M.pi x τ).2.1 ht) z

theorem realRegP_of_nonpos (x : ParabolicSpace) (d : ι) {t : ℝ} (ht : t ≤ 0) (z : ParabolicSpace) :
    realRegP M h x d t z = 0 := by
  simp [realRegP, not_lt.2 ht]

include H in
theorem piExt_gammaExtMap (x y : ParabolicSpace) (w : ι' → ℝ) :
    H.piExt x (H.gammaExtMap x y w) = H.piExt y w := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = mkVec E.old E.new D a b := ⟨_, _, E.eq_mkVec w⟩
  unfold gammaExtMap
  rw [E.gammaExt_mkVec]
  refine Subtype.ext (funext fun t => funext fun z => ?_)
  rw [H.regPi_piExt_mkVec, H.regPi_piExt_mkVec]
  set δ : ι → ℝ := projD D b with hδ
  set G : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := M.gammaMap x y with hG
  by_cases ht : t ≤ 0
  · simp only [regPi_eq_zero_of_nonpos, realRegP_of_nonpos _ _ ht, ht, mul_zero,
      Finset.sum_const_zero, add_zero]
  · rw [not_le] at ht
    obtain ⟨hext, hlow⟩ := H.gammaMap_mem_ext_lower x y b
    have key1 := H.regPi_ext_identity hext hlow x ht z
    have hfun : (fun t w => M.regPi x (G δ) t w) = fun t w => M.regPi y δ t w := by
      funext t' w'
      exact M.regPi_gammaMap x y δ t' w'
    rw [hfun] at key1
    have key2 := H.regPi_ext_identity (H.projD_mem_ext_lower b).1 (H.projD_mem_ext_lower b).2 y
      ht z
    have hIδ : I δ = 0 := map_projD E.I_D b
    rw [hIδ, zero_add] at key2
    have hsum : ∑ d ∈ D, δ d * realRegP M h y d t z = ∑ d ∈ D, b d * realRegP M h y d t z :=
      Finset.sum_congr rfl fun d hd => by rw [hδ, projD_apply_of_mem hd]
    rw [hsum] at key2
    have e1 : M.regPi x (G a + I (G δ) + (jMapP M h P x) (G δ) - G (jMapP M h P y δ)) t z =
        M.regPi y a t z + M.regPi x (I (G δ) + (jMapP M h P x) (G δ)) t z -
          M.regPi y (jMapP M h P y δ) t z := by
      rw [M.regPi_sub, M.regPi_add, M.regPi_add, M.regPi_add]
      have a1 := M.regPi_gammaMap x y a t z
      have a2 := M.regPi_gammaMap x y (jMapP M h P y δ) t z
      simp only [hG] at a1 a2 ⊢
      rw [a1, a2]
      ring
    rw [e1]
    linarith

end IntExtHyp

end RegularityStructures

end
