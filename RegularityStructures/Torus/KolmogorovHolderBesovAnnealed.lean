/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovMoment
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Tonelli input for the torus Kolmogorov criterion

The pointwise annealed heat estimate is converted to a spatially integrated one by Tonelli.  The
joint almost-everywhere measurability assumption is explicit, so this theorem does not hide a
measurability assertion about a random field or its heat regularisation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

theorem heatMoment_lintegral_swap_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {X : Ω → C(Torus3, ℝ)} {p : ℕ} {r α A : ℝ}
    (hjoint : AEMeasurable
      (fun z : Ω × Torus3 =>
        ‖heatSemigroup r (X z.1) z.2‖ₑ ^ p) (P.prod volume))
    (hpoint : ∀ y : Torus3,
      ∫⁻ ω, ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2))) :
    ∫⁻ ω, ∫⁻ y : Torus3,
        ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂volume ∂P ≤
      ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := by
  calc
    ∫⁻ ω, ∫⁻ y : Torus3,
        ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂volume ∂P =
        ∫⁻ y : Torus3, ∫⁻ ω,
          ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ∂volume := by
      exact lintegral_lintegral_swap (f := fun ω : Ω => fun y : Torus3 =>
        ‖heatSemigroup r (X ω) y‖ₑ ^ p) hjoint
    _ ≤ ∫⁻ _y : Torus3, ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := by
      exact lintegral_mono (fun y => hpoint y)
    _ = ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := by
      have hadd :
          (MeasureTheory.Measure.addHaarMeasure
              (⊤ : TopologicalSpace.PositiveCompacts (AddCircle (1 : ℝ))))
              Set.univ = 1 := by
        simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
          (MeasureTheory.Measure.addHaarMeasure_self
            (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (AddCircle (1 : ℝ)))))
      simp only [MeasureSpace.volume]
      rw [lintegral_const]
      simp [Measure.pi_univ, hadd]

end RegularityStructures

end
