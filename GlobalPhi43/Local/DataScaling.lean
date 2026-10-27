module

public import GlobalPhi43.Local.HeatOperatorTransport
public import GlobalPhi43.MW20.Setting.IsMWLocalData

public section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped ContDiff

/-- Global source tree smoothness is preserved; local solution smoothness is
handled separately on the preimage of its actual neighbourhood. -/
theorem parabolicPullback_contDiff (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parabolicPullback a f b ℓ) := by
  rw [← contDiffOn_univ]
  simpa only [preimage_univ] using parabolicPullback_contDiffOn a f b ℓ (O := univ) hf.contDiffOn

theorem heatOperator_parabolicPullback_global (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (hf : ContDiff ℝ ∞ f) (x : ParabolicSpace) :
    heatOperator (parabolicPullback a f b ℓ) x = a*ℓ^2*heatOperator f (parabolicMap b ℓ x) :=
  heatOperator_parabolicPullback a f b ℓ isOpen_univ hf.contDiffOn x (mem_univ _)

end GlobalPhi43.Local
