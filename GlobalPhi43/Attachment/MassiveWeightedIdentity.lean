module

public import GlobalPhi43.Attachment.MassiveMildIdentity

/-! Removing the massive exponential from the actual potential identity. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.PDE Set

/-- The actual exponentially weighted potential satisfies an ordinary heat semigroup identity. -/
theorem massivePotential_weighted_identity {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    {s t : ℝ} (hst : s ≤ t) :
    Real.exp t • ψ t = Real.exp s • heatOp (t-s) (ψ s) +
      ∫ r in Ioc s t, Real.exp r • heatOp (t-r)
        (potSlice (attachment_potForcing hf hg).cont r) := by
  have he (r : ℝ) : Real.exp t * Real.exp (-(t-r)) = Real.exp r := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp t • ψ t = Real.exp t •
        (Real.exp (-(t-s)) • heatOp (t-s) (ψ s) +
          ∫ r in Ioc s t, potF (attachment_potForcing hf hg).cont t r) :=
      congrArg (fun u => Real.exp t • u) (massivePotential_mild_identity hf hg hψ hst)
    _ = Real.exp s • heatOp (t-s) (ψ s) +
        ∫ r in Ioc s t, Real.exp r • heatOp (t-r)
          (potSlice (attachment_potForcing hf hg).cont r) := by
      rw [smul_add, smul_smul, he s, ← integral_smul]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r _
      change Real.exp t • (Real.exp (-(t-r)) • _) = _
      rw [smul_smul, he r]

end GlobalPhi43.Attachment
