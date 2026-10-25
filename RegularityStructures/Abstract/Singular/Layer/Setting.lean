/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox
public import RegularityStructures.Abstract.Singular.Layer.Geometry
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The setting of the layer bound

`LayerSetting M f γ η α Cf CPi CGam T` bundles the hypotheses of Hairer's Proposition 6.9 in the
form used for the lattice approximation: the model bounds, `f ∈ D^{γ,η}_P` on the slab
`(0, T] × ℝ³` with constant `Cf`, vanishing outside the slab, and values in a sector of regularity
`α` with `α ∧ η > −2`.

`abs_pairing_regPi_lattice_le` is the sup-bound for a single lattice point: for a test function
scaled at `z_{q,k}` with radius `8 · 2^{-q}`,
`|⟨Π_z f(z), g⟩| ≤ C K₀ Cf A (2^{-q})^{5 + α ∧ η}`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}

theorem pairing_regPi_zero_eq (M : Model 𝒯 parabolicSemigroup) (z : ParabolicSpace)
    (g : ParabolicSpace → ℝ) : parabolicSemigroup.pairing (M.regPi z 0) g = 0 := by
  unfold RegularisingSemigroup.pairing
  have : (fun s => ∫ y, M.regPi z 0 s y * g y) = fun _ => 0 := by
    funext s
    simp [Model.regPi]
  rw [this]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

end RegularityStructures

end
