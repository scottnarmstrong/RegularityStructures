/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyModelBound
public import RegularityStructures.Abstract.QFamilyR4Convolution
public import RegularityStructures.Abstract.RegularityStructure
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Hairer's model bound (2.15) on `ℝ⁴` from the `Q`-form bound

For the auxiliary semigroup on `ℝ⁴`, a model with `|(Q_t Π_x e_i)(x)| ≤ C_Π t^{deg i/4}` and
`|(Γ_{yx} e_i)_j| ≤ C_Γ d(y, x)^{deg i − deg j}`, all homogeneities below `γ` larger than `-4`:

  `|⟨Π_x e_i, φ^λ_x⟩| ≤ r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π · λ^{deg i}`

for `deg i < γ`, `φ ∈ B^4`, `0 < λ ≤ 1` and every `x`, the pairing existing
(`Model.abs_pairing_regPi_rescaledTestFunction_le`). The constant `r4ModelConst 𝒯 γ` depends only
on the regularity structure and `γ`, uniformly over `deg i < γ`, as in [Hai14, (2.15)].

Source: [Hai14] = arXiv:1303.5113v4, Definition 2.17, (2.15).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant of the test-function model bound on `ℝ⁴`. -/
def r4ModelConst (𝒯 : RegularityStructure ι) (γ : ℝ) : ℝ :=
  Fintype.card ι * parabolicSemigroup.pairingConst (𝒯.degreesBelow γ) *
    (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff))

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

theorem RegularisingSemigroup.pairingConst_le_of_subset {E : Type*} [MeasurableSpace E]
    {μ : Measure E} (K : RegularisingSemigroup E μ) {A A' : Finset ℝ} (h : A ⊆ A')
    (hA' : ∀ a ∈ A', -K.order < a) : K.pairingConst A ≤ K.pairingConst A' :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun a ha _ => by
    have : 0 < a + K.order := by linarith [hA' a ha]
    have : 0 ≤ K.order / (a + K.order) := div_nonneg K.order_pos.le this.le
    linarith

end RegularityStructures

end
