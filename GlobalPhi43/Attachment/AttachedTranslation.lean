module

public import GlobalPhi43.Attachment.NoiseGrowthTranslate
public import GlobalPhi43.Attachment.TranslateIdentification

/-! Norm covariance for the actual chosen model, on and off the exact growth event. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43

open scoped ContDiff in
/-- Smoothness of a periodic noise is preserved by a real time shift. -/
theorem smooth_time_translate {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (k : ℝ) :
    IsSmoothOnSpaceTime (fun z => f (z.1 + k, z.2)) := by
  have h := hf.comp (contDiff_id.add (contDiff_const (c := ((k, 0) : ParabolicSpace))))
  change ContDiff ℝ ∞ (fun w : ParabolicSpace => f (w.1 + k, torusProj w.2))
  have he : (fun w : ParabolicSpace => f (w.1 + k, torusProj w.2)) =
      (fun p : ParabolicSpace => f (p.1, torusProj p.2)) ∘
        (fun x => id x + ((k, 0) : ParabolicSpace)) := by
    funext w
    dsimp
    rw [add_zero]
  rw [he]
  exact h

end GlobalPhi43.Attachment
