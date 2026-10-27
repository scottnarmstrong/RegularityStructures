module

public import GlobalPhi43.Attachment.Pairing
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit

/-! Identifying the small-scale pairing limit with an ordinary realisation integral. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory Filter RegularityStructures
open scoped Topology ContDiff

/-- The LocalBall estimate bounds the ordinary integral once a continuous polynomially growing
realisation is attached. These are the concrete premises needed at the small-scale conversion. -/
theorem integral_realisation_le {Λ : ℝ → ParabolicSpace → ℝ} {g : ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {γ : ℝ} {A : Finset ℝ} {C lam : ℝ}
    (hΛ : parabolicSemigroup.LocalBall Λ x₀ γ A C lam) (hA : ∀ a ∈ A, -4 < a)
    (hg : Continuous g) (hgm : PolyBounded g)
    (hreal : ∀ t, 0 < t → ∀ z, Λ t z = parabolicSemigroup.apply t g z)
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hs : parabolicSemigroup.IsSupported φ x₀ lam)
    (hφ1 : ∫ y, |φ y| ≤ B₀)
    (hψ1 : ∫ y, |parabolicGenerator φ y| ≤ B₁ * lam ^ (-4 : ℝ)) :
    |∫ y, g y * φ y| ≤ C * parabolicSemigroup.pairingConst A * (B₀ + B₁) * lam ^ γ := by
  obtain ⟨L, hL, hbound⟩ := pairing_le hΛ hA hφ hc hlam hlam1 hs hφ1 hψ1
  obtain ⟨_, B, n, hB⟩ := hgm
  have he : (fun s => ∫ y, Λ s y * φ y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s => ∫ y, parabolicSemigroup.apply s g y * φ y) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp_rw [hreal s hs]
  have hi := (tendsto_integral_apply_mul hg hB hφ.continuous hc).congr' he.symm
  have hident : L = ∫ y, g y * φ y := tendsto_nhds_unique hL hi
  rwa [hident] at hbound

end GlobalPhi43.Attachment
