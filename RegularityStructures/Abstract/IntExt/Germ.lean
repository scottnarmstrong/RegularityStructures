/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Sector
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Germ
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The planted germs `Q_t g_{x,d}`

Under `IntExtHyp`, with `V₂ = V ⊔ span D`: for `d ∈ D` the germ `realGermP M h x d` has polynomial
growth and `realRegP M h x d` is a `Q`-distribution (`realRegP_mem_ext`), and
[Hai14, Remark 5.10, (5.17)]

  `Q_t Π_x J(x) e_j + realRegP M h x j t = Q_t (K ∗ Π_x e_j)`     (`regPi_jMapP_add_realRegP`)

for `e_j ∈ V` or `j ∈ D`, `deg j < γ`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

namespace IntExtHyp

open IntExt

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {𝒯 : RegularityStructure ι} {𝒯' : RegularityStructure ι'} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {P' : PolynomialSector 𝒯' N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {D : Finset ι} {M : Model 𝒯 parabolicSemigroup} {E : IntegrationExtension 𝒯 𝒯' P P' I D}
  {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ} {V : Submodule ℝ (ι → ℝ)}
  (H : IntExtHyp M E h N γ V)

include H in
/-- The germ of `Π_x I e_j`, for `e_j ∈ V` or `j ∈ D`, has polynomial growth. -/
theorem polyBounded_realGermP_ext {j : ι} (hj : (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D)
    (hjγ : 𝒯.deg j < γ) (x : ParabolicSpace) : PolyBounded (realGermP M h x j) := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  have hj2 := H.single_mem_ext_of_mem hj
  have hR := G.kRegularG_regPi_single H.isSector_ext H.coord_ext H.deg_gt_ext hj2 hjγ x
  have hK := hR.polyBounded_kConv_growthP H.profile
  have hσ := polyBounded_polyEval x (jPolyCoeffP (N' := N') M h x j)
  have e : realGermP M h x j = fun w => kConvP h (fun t w => M.regPi x (Pi.single j 1) t w) w -
      polyEval x (jPolyCoeffP (N' := N') M h x j) w := by
    funext w
    rw [realGerm_eq_growthP M H.profile G H.isSector_ext H.coord_ext H.deg_gt_ext hj2 hjγ x w,
      polyEval_jPolyCoeffP M h x j (H.poly_deg_ext j hj2 hjγ) w]
  rw [e]
  exact hK.sub hσ

include H in
/-- `realRegP M h x d` is a `Q`-distribution for `d ∈ D`. -/
theorem realRegP_mem_ext {d : ι} (hd : d ∈ D) (x : ParabolicSpace) :
    realRegP M h x d ∈ parabolicSemigroup.distributions :=
  mem_distributions_ite_apply (H.polyBounded_realGermP_ext (Or.inr hd) (H.deg_D d hd) x)

include H in
/-- `Q_t Π_x J(x) e_j + Q_t g_{x,j} = Q_t (K ∗ Π_x e_j)` [Hai14, Remark 5.10, (5.17)]. -/
theorem regPi_jMapP_add_realRegP {j : ι} (hj : (Pi.single j 1 : ι → ℝ) ∈ V ∨ j ∈ D)
    (hjγ : 𝒯.deg j < γ) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (jMapP M h P x (Pi.single j 1)) t z + realRegP M h x j t z =
      parabolicSemigroup.apply t (kConvP h (fun t w => M.regPi x (Pi.single j 1) t w)) z := by
  obtain ⟨C, C', p, q, ρP, ρG, G⟩ := H.growth
  have hj2 := H.single_mem_ext_of_mem hj
  have hR := G.kRegularG_regPi_single H.isSector_ext H.coord_ext H.deg_gt_ext hj2 hjγ x
  have hK := hR.polyBounded_kConv_growthP H.profile
  have hσ := polyBounded_polyEval x (jPolyCoeffP (N' := N') M h x j)
  have hG := H.polyBounded_realGermP_ext hj hjγ x
  rw [jMapP_single, jVec_eq_polyEmbedP, Model.regPi_polyEmbed H.realising.poly,
    polyReg_of_pos _ _ ht, realRegP_of_pos M h x j ht, add_comm, ← hG.apply_add hσ ht z]
  congr 1
  funext w
  rw [realGerm_eq_growthP M H.profile G H.isSector_ext H.coord_ext H.deg_gt_ext hj2 hjγ x w,
    polyEval_jPolyCoeffP M h x j (H.poly_deg_ext j hj2 hjγ) w]
  ring

end IntExtHyp

end RegularityStructures

end
