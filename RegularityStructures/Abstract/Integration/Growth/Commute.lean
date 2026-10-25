/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.KConv
public import RegularityStructures.Abstract.Integration.Growth.Bundle
public import RegularityStructures.Abstract.Integration.Sector.Commute
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Integration.Realising.Germ
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Input of Hairer's Lemma 5.16 under weighted bounds

For a model `M` satisfying the weighted bounds `Model.GrowthModel` and a sector `V` whose basis
vectors below `γ` have degrees `> -2`, `Π_x e_i` is `KRegularG` at `x`, that is of local order
with growth and exponents above `-2` (`Model.GrowthModel.kRegularG_regPi_single`). Hence
`K ∗ Π_x e_i` is a function of polynomial growth, which is the input of the proof of
`Γ_{xy} (I + J(y)) a = (I + J(x)) Γ_{xy} a` [Hai14, Lemma 5.16] under weighted bounds
(`RegularityStructures.Abstract.Profile.Growth.Commute`).
Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.16.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  {N : ℕ} {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- `Π_x e_i`, `e_i ∈ V`, is `KRegularG` at `x` if the basis vectors of `V` below `γ` have
degrees `> -2`. -/
theorem GrowthModel.kRegularG_regPi_single (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x : ParabolicSpace) :
    KRegularG (fun t z => M.regPi x (Pi.single i 1) t z) x :=
  ⟨regPi_single_mem_distributions M x i, fun _ hu => M.measurable_pi x i hu,
    𝒯.deg i, max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x), p + qG,
    𝒯.degreesBelowLeIn V γ (𝒯.deg i), degreesBelowLeIn_bounds_two hdeg i,
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _))
      (mul_nonneg (G.moderateP.pos x).le (G.moderateG.pos x).le),
    add_nonneg G.moderateP.nonneg_exp G.nonnegG,
    M.isLocalOrderGrowth_regPi_single_in hV hVb G.moderateP G.moderateG.one_le G.nonnegG
      G.piBound G.gammaBound G.piBound_nonneg hVi hi x⟩

end Model

end RegularityStructures

end
