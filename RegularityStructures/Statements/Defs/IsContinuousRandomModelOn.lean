/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Continuous random models

A family `Z : Ω → Model 𝒯` of models is a continuous random model on a set `S` if the regularised
realisations `(Q_t Π_x e_i)(x)` and the entries of `Γ_{yx}` are measurable in `ω`, and if, for every
`ω`, the map `(t, x) ↦ (Q_t Π_x e_i)(x)` is continuous on `(0, 1] × S` and the entries of `Γ_{yx}`
are continuous in `(x, y) ∈ S × S`. Continuity makes the suprema that define the model norms on
`S` measurable, so that their moments are defined.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Realisations of a random model are measurable in `ω` and continuous on `S`. -/
def IsContinuousRandomModelOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructures.RegularityStructure ι} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup)
    (S : Set RegularityStructures.ParabolicSpace) : Prop :=
  (∀ (i : ι) (x : RegularityStructures.ParabolicSpace) (t : ℝ), 0 < t →
      Measurable fun ω => (Z ω).regPi x (Pi.single i 1) t x) ∧
    (∀ (i j : ι) (x y : RegularityStructures.ParabolicSpace),
      Measurable fun ω => (Z ω).gammaMap y x (Pi.single i 1) j) ∧
    (∀ ω (i : ι), ContinuousOn
      (fun w : ℝ × RegularityStructures.ParabolicSpace =>
        (Z ω).regPi w.2 (Pi.single i 1) w.1 w.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ S)) ∧
    ∀ ω (i j : ι), ContinuousOn
      (fun w : RegularityStructures.ParabolicSpace × RegularityStructures.ParabolicSpace =>
        (Z ω).gammaMap w.2 w.1 (Pi.single i 1) j) (S ×ˢ S)

end RegularityStructures

end
