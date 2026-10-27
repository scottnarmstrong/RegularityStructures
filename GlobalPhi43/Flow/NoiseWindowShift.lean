module

public import GlobalPhi43.Markov.NoiseWindows
public import GlobalPhi43.Attachment.NoiseTranslation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact time transport of the completed noise windows. No action on
the underlying sample space is assumed. -/

public noncomputable section

open MeasureTheory Set RegularityStructures

namespace GlobalPhi43.Flow

/-- Time translation acts on tests on the same probability space. -/
@[expose] def shiftWhiteNoise {Ω : Type*} (W : (SpaceTime → ℝ) → Ω → ℝ) (s : ℝ) :
    (SpaceTime → ℝ) → Ω → ℝ := fun h => W (fun z => h (z.1 - s, z.2))

theorem shiftWhiteNoise_zero {Ω : Type*} (W : (SpaceTime → ℝ) → Ω → ℝ) :
    shiftWhiteNoise W 0 = W := by
  funext h
  change W (fun z => h (z.1 - 0, z.2)) = W h
  simp only [sub_zero, Prod.mk.eta]

end GlobalPhi43.Flow
