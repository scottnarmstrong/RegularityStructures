/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Gamma

/-!
# The cocycle identities for the extended group maps

`gammaExt_self`: `Γ'_{xx} = 1` and `gammaExt_comp`: `Γ'_{xy} Γ'_{yz} = Γ'_{xz}`, the algebraic form
of [Hai14, Theorem 5.14, proof].  For the composition one needs a `G`-invariant subspace `W` of `T`
(later `V ∩ T_{<γ}`) without `D`-coordinates which supplements `span D` in `Γ_{yz} span D`, and
Lemma 5.16 for `(I, J)` on `W`: `Γ_{xy} (I + J(y)) w = (I + J(x)) Γ_{xy} w`.
-/

public section

namespace RegularityStructures

namespace IntegrationExtension

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} (E : IntegrationExtension 𝒯 𝒯' P P' I D)

/-- `Γ'_{xx} = 1`. -/
theorem gammaExt_self (J : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    E.gammaExt LinearMap.id J J = LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = mkVec E.old E.new D a b := ⟨_, _, E.eq_mkVec w⟩
  rw [E.gammaExt_mkVec]
  simp only [LinearMap.id_apply, map_projD E.I_D, add_zero, add_sub_cancel_right]
  exact mkVec_congr fun d hd => projD_apply_of_mem hd b

/-- The cocycle identity `Γ'_{xy} Γ'_{yz} = Γ'_{xz}`, for the extended maps built from
`Γ_{xy}`, `Γ_{yz}`, `Γ_{xz}` (the first three arguments, in this order) and from `J(x)`, `J(y)`,
`J(z)` (the last three). -/
theorem gammaExt_comp (G1 G2 G3 Jx Jy Jz : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hG : G1 ∘ₗ G2 = G3)
    (W : Submodule ℝ (ι → ℝ)) (hW : ∀ w ∈ W, G1 w ∈ W) (hWD : ∀ w ∈ W, ∀ d ∈ D, w d = 0)
    (hsupp : ∀ b, G2 (projD D b) - projD D (G2 (projD D b)) ∈ W)
    (h516 : ∀ w ∈ W, G1 (I w + Jy w) = I (G1 w) + Jx (G1 w)) :
    E.gammaExt G1 Jx Jy ∘ₗ E.gammaExt G2 Jy Jz = E.gammaExt G3 Jx Jz := by
  have hG' : ∀ v, G1 (G2 v) = G3 v := fun v => by rw [← hG]; rfl
  refine LinearMap.ext fun w => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = mkVec E.old E.new D a b := ⟨_, _, E.eq_mkVec w⟩
  simp only [LinearMap.comp_apply]
  rw [E.gammaExt_mkVec, E.gammaExt_mkVec, E.gammaExt_mkVec]
  have hw := hsupp b
  have hIδ : I (projD D (G2 (projD D b))) = 0 := map_projD E.I_D _
  have hG3 : G3 (projD D b) = G1 (G2 (projD D b)) := (hG' _).symm
  generalize projD D (G2 (projD D b)) = δ' at hw hIδ ⊢
  generalize hgg : G2 (projD D b) = g at hw hG3 ⊢
  obtain ⟨w', hw'W, rfl⟩ : ∃ w' ∈ W, g = δ' + w' := ⟨g - δ', hw, by abel⟩
  have hb : ∀ d ∈ D, G1 δ' d = G3 (projD D b) d := fun d hd => by
    rw [hG3, map_add, Pi.add_apply, hWD _ (hW _ hw'W) d hd, add_zero]
  have hA : G1 (G2 a + I (δ' + w') + Jy (δ' + w') - G2 (Jz (projD D b))) + I (G1 δ') +
      Jx (G1 δ') - G1 (Jy δ') = G3 a + I (G3 (projD D b)) + Jx (G3 (projD D b)) -
      G3 (Jz (projD D b)) := by
    have h5 := h516 w' hw'W
    rw [hG3]
    simp only [map_add, map_sub, hG', hIδ, map_zero] at h5 ⊢
    linear_combination (norm := module) h5
  rw [hA]
  exact mkVec_congr hb

end IntegrationExtension

end RegularityStructures

end
