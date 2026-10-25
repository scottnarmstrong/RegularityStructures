/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovHSGlobalOffDiagonalMeasurable

/-!
# Measurability consequences of continuity of the regularised fields

The predicate `IsContinuousRandomModelWithFieldsOn` asks, in addition to continuous realisations,
that the regularised fields `(t, y) ↦ (Q_t Π_x e_i)(y)` be continuous. This module proves the
Carathéodory consequences used by the semigroup proof.
-/

@[expose] public section

namespace RegularityStructures

open MeasureTheory

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω]
  {𝒯 : RegularityStructures.RegularityStructure ι}
  {Z : Ω → RegularityStructures.Model 𝒯
    RegularityStructures.parabolicSemigroup}
  {S : Set RegularityStructures.ParabolicSpace}

/-- Continuity of the regularised fields upgrades every fixed positive-time off-diagonal field to a
jointly measurable function of the random variable and evaluation point. -/
theorem IsContinuousRandomModelWithFieldsOn.offDiagonal_regPi_jointMeasurable
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S) (i : ι)
    (x : RegularityStructures.ParabolicSpace) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    Measurable (fun z : Ω × RegularityStructures.ParabolicSpace =>
      (Z z.1).regPi x (Pi.single i 1) u z.2) := by
  let f : RegularityStructures.ParabolicSpace → Ω → ℝ := fun y ω =>
    (Z ω).regPi x (Pi.single i 1) u y
  have hcont : ∀ ω, Continuous (fun y => f y ω) := by
    intro ω
    have h := hZ.2 ω i x
    have hc := h.comp_continuous
      (continuous_const.prodMk continuous_id)
      (fun y : RegularityStructures.ParabolicSpace => ⟨hu, Set.mem_univ y⟩)
    exact hc
  have hmeas : ∀ y, Measurable (f y) := by
    intro y
    exact RegularityStructures.hsGlobal_offDiagonal_regPi_measurable
      hZ.1 i x y hu.1
  have huncurry : Measurable (Function.uncurry f) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hswap : Measurable (fun z : Ω × RegularityStructures.ParabolicSpace =>
      (z.2, z.1)) := measurable_swap
  have heq : (fun z : Ω × RegularityStructures.ParabolicSpace =>
      (Z z.1).regPi x (Pi.single i 1) u z.2) =
      (Function.uncurry f) ∘ (fun z : Ω × RegularityStructures.ParabolicSpace =>
        (z.2, z.1)) := by
    funext z
    rfl
  rw [heq]
  exact huncurry.comp hswap

/- The same Carathéodory argument retains the positive time variable. -/

end RegularityStructures

end
