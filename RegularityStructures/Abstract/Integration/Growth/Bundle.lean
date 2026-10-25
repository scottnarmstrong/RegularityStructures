/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Integration.Sector.Coeff
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Basic
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# The standing hypotheses on a distribution of local order with growth

`LocalGrowth Λ x γ A C q` bundles what the weighted pairing estimates need about a `Q`-family
`Λ` on `ℝ⁴`: `Λ` is a measurable distribution, the exponents `A` lie in `(-4, γ]`, the
constants are nonnegative and `Λ` is of order `γ` at `x` with growth `q`
(`IsLocalOrderGrowth`). It is provided for `Π_x e_i` (`Model.GrowthModel.localGrowth_regPi`) and
for `Rf − Π_x f(x)` (`Model.GrowthData.localGrowth_reconstructSubAt`), with sector exponents.
-/

@[expose] public section

open MeasureTheory Set

namespace RegularityStructures

/-- A measurable distribution on `ℝ⁴` of order `γ` at `x` with exponents `A ⊆ (-4, γ]`,
constant `C ≥ 0` and growth `q ≥ 0`. -/
structure LocalGrowth (Λ : ℝ → ParabolicSpace → ℝ) (x : ParabolicSpace) (γ : ℝ) (A : Finset ℝ)
    (C q : ℝ) : Prop where
  mem : Λ ∈ parabolicSemigroup.distributions
  meas : ∀ u, 0 < u → Measurable (Λ u)
  exps : ∀ a ∈ A, -4 < a ∧ a ≤ γ
  nonneg : 0 ≤ C
  nonneg_exp : 0 ≤ q
  loc : parabolicSemigroup.IsLocalOrderGrowth Λ x γ A C q

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam Cf p qG qf : ℝ}
  {ρP ρG ρf : ParabolicSpace → ℝ} {f : ParabolicSpace → ι → ℝ}

/-- `Π_x e_i`, `e_i ∈ V`, is of local order `deg i` at `x` with growth `p + qG`
(`isLocalOrderGrowth_regPi_single_in`). -/
theorem GrowthModel.localGrowth_regPi (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x : ParabolicSpace) :
    LocalGrowth (fun t z => M.regPi x (Pi.single i 1) t z) x (𝒯.deg i)
      (𝒯.degreesBelowLeIn V γ (𝒯.deg i))
      (max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x)) (p + qG) where
  mem := M.regPi_mem x _
  meas _ hu := M.measurable_regPi x _ hu
  exps := degreesBelowLeIn_bounds 𝒯 V hdeg i
  nonneg := mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
    G.piBound_nonneg) (Nat.cast_nonneg _))
    (mul_nonneg (G.moderateP.pos x).le (G.moderateG.pos x).le)
  nonneg_exp := add_nonneg G.moderateP.nonneg_exp G.nonnegG
  loc := M.isLocalOrderGrowth_regPi_single_in hV hVb G.moderateP G.moderateG.one_le G.nonnegG
    G.piBound G.gammaBound G.piBound_nonneg hVi hi x

end Model

end RegularityStructures

end
