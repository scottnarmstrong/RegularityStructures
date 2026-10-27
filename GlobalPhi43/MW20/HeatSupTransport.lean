module

public import GlobalPhi43.MW20.HeatTransport
public import GlobalPhi43.Local.AffineTransport

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set

/-- The actual local heat supremum transports with its exact amplitude,
including possibly infinite values and without an input PDE estimate. -/
theorem localScalarSup_sourceHeat_parabolicPullback (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ParabolicSpace) (R : ℝ) :
    localScalarSup (sourceHeat (parabolicPullback a f b ℓ)) (pastBall x R) =
      ENNReal.ofReal |a*ℓ^2| *
        localScalarSup (sourceHeat f) (pastBall (parabolicMap b ℓ x) (ℓ*R)) := by
  have he : sourceHeat (parabolicPullback a f b ℓ) =
      parabolicPullback (a*ℓ^2) (sourceHeat f) b ℓ :=
    funext (sourceHeat_parabolicPullback a f b ℓ)
  rw [he,localScalarSup_parabolicPullback,parabolicMap_image_pastBall b hℓ]

end GlobalPhi43.MW20
