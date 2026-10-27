module

public import GlobalPhi43.Attachment.MassiveRegularity
public import Phi43.Potential.TruncIdentity

/-! Exact truncated Duhamel identity for the actual massive potential.
The exponential factor is retained; the unweighted J-minus-potential identity is separate. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.PDE Set

/-- The actual potential satisfies its exact massive semigroup identity at arbitrary start times. -/
theorem massivePotential_mild_identity {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    {s t : ℝ} (hst : s ≤ t) :
    ψ t = Real.exp (-(t-s)) • heatOp (t-s) (ψ s) +
      ∫ r in Ioc s t, potF (attachment_potForcing hf hg).cont t r := by
  rw [integral_potF_Ioc (attachment_potForcing hf hg) hψ hst]
  abel

end GlobalPhi43.Attachment
