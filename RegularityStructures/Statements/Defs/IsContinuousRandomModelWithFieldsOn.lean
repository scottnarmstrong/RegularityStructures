/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelOn

/-!
# Continuous random models with continuous regularised fields

A continuous random model on `S` (`IsContinuousRandomModelOn`) whose regularised fields
`(t, y) ↦ (Q_t Π_x e_i)(y)` are, in addition, continuous on `(0, 1] × ℝ⁴` for every base point `x`,
not only on the diagonal over `S`. This makes the regularised fields jointly measurable in `(ω, y)`
on the whole space, which the Kolmogorov criterion for the model norms (`kolmogorov_modelNorm`)
needs.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Realisations of a random model are measurable in `ω` and continuous on `S` (as in
`IsContinuousRandomModelOn`), and every regularised field `(t, y) ↦ (Q_t Π_x e_i)(y)` is continuous
on `(0, 1] × ParabolicSpace`, for every base point `x`. -/
def IsContinuousRandomModelWithFieldsOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructures.RegularityStructure ι} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup)
    (S : Set RegularityStructures.ParabolicSpace) : Prop :=
  RegularityStructures.IsContinuousRandomModelOn Z S ∧
    ∀ ω (i : ι) (x : RegularityStructures.ParabolicSpace), ContinuousOn
      (fun w : ℝ × RegularityStructures.ParabolicSpace =>
        (Z ω).regPi x (Pi.single i 1) w.1 w.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.univ)

end RegularityStructures
