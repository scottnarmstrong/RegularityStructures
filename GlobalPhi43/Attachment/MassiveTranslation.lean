module

public import RegularityStructures.Statements.Defs.IsMassivePotential
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Ring

/-! Translation of the massive-potential input, including absolute integrability. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures

/-- Time translation of the stationary massive potential with exactly the translated forcing. -/
theorem massivePotential_time_translate {f : SpaceTime → ℝ}
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (k : ℝ) :
    IsMassivePotential (fun z => f (z.1 + k, z.2)) (fun t => ψ (t + k)) := by
  let e : SpaceTime ≃ᵐ SpaceTime :=
    (MeasurableEquiv.addRight k).prodCongr (MeasurableEquiv.refl Torus3)
  have hmp : MeasurePreserving e (volume : Measure SpaceTime) volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right (volume : Measure ℝ) k).prod (MeasurePreserving.id volume)
  have heq (w : SpaceTime) : e w = w + (k, 0) := by
    apply Prod.ext
    · rfl
    · change w.2 = w.2 + 0
      rw [add_zero]
  have he (t : ℝ) (x : Torus3) (w : SpaceTime) :
      massiveHeatKernel ((t + k, x) - (w + (k, 0))) * f (w + (k, 0)) =
        massiveHeatKernel ((t, x) - w) * f (w.1 + k, w.2) := by
    have hsub : ((t + k, x) : SpaceTime) - (w + (k, 0)) = (t, x) - w := by
      apply Prod.ext
      · change t + k - (w.1 + k) = t - w.1
        ring
      · change x - (w.2 + 0) = x - w.2
        rw [add_zero]
    have hadd : w + ((k, 0) : SpaceTime) = (w.1 + k, w.2) := by
      apply Prod.ext
      · rfl
      · change w.2 + 0 = w.2
        rw [add_zero]
    rw [hsub, hadd]
  constructor
  · intro t x
    have h := hmp.integrable_comp_of_integrable (hψ.1 (t + k) x)
    simpa only [Function.comp_def, heq, he] using h
  · intro t x
    rw [hψ.2]
    rw [← hmp.integral_comp'
      (fun w : SpaceTime => massiveHeatKernel ((t + k, x) - w) * f w)]
    simp only [heq, he]

end GlobalPhi43.Attachment
