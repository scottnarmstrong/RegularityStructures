module

public import GlobalPhi43.MW20.HeatSupTransport

public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set

@[simp] theorem parabolicPullback_one (f : ParabolicSpace → ℝ) (b : ParabolicSpace)
    (ℓ : ℝ) : parabolicPullback 1 f b ℓ = fun y => f (parabolicMap b ℓ y) := by
  funext y
  simp only [parabolicPullback,one_mul]

/-- Amplitude-one affine-error transport, directly usable by unit caloric consumers. -/
theorem pastAffineError_comp_parabolicMap (f : ParabolicSpace → ℝ) (b : ParabolicSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ParabolicSpace) (R : ℝ) :
    pastAffineError (fun y => f (parabolicMap b ℓ y)) x R =
      pastAffineError f (parabolicMap b ℓ x) (ℓ*R) := by
  simpa only [parabolicPullback_one,one_mul,abs_one,ENNReal.ofReal_one] using
    pastAffineError_parabolicPullback 1 one_ne_zero f b hℓ x R

end GlobalPhi43.Local
