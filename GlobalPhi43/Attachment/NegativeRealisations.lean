module

public import GlobalPhi43.Attachment.KernelIntegrability
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit

/-! Function realisations for every negative symbol, with continuity and growth attached. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Filter
open scoped Topology

/-- The noise-growth hypothesis supplies a simultaneous family of continuous polynomially bounded negative realisations,
with the exact Q-regularisation identity at every positive scale. -/
theorem exists_negative_model_realisations {N : ℕ} {κ : Kappa} {f₀ : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hg : Statements.HasPhi43NoiseGrowth f₀)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f₀ C Z) :
    ∃ g : ParabolicSpace → Symbol → ParabolicSpace → ℝ,
      (∀ x τ, Continuous (g x τ) ∧ PolyBounded (g x τ)) ∧
      (∀ x τ, τ ∈ fMinus → ∀ t, 0 < t → ∀ y,
        Z.regPi x (Pi.single τ 1) t y = parabolicSemigroup.apply t (g x τ) y) := by
  obtain ⟨noise, hn, hRC, _⟩ := regPi_fMinus hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have hz : noise.zeta = fun w : ParabolicSpace => f₀ (w.1, torusProj w.2) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [hz]; exact hgr
  let g := fun x τ => (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ)
  refine ⟨g, ?_, ?_⟩
  · intro x τ
    exact ⟨(renormalisedExtensionPi_smooth N noise C x (basis τ)).continuous,
      renormalisedExtensionPi_growth N noise
        (canonicalNoise_polyBounded_of_derivatives noise Cg q hg') C x (basis τ)⟩
  · intro x τ hτ t ht y
    have hcan := canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg' C
    have hcoord : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
      apply phi43CoordinateEquiv.injective
      simp only [LinearEquiv.apply_symm_apply, phi43CoordinateEquiv_basis]
    rw [regPi_eq_of_isRenormalisedCanonicalModel hRC hcan (Or.inl hτ) x ht y,
      canonicalRenormalisedModel_regPi N κ noise Cg q hg' C x _ ht y, hcoord]

/-- Uniqueness of a continuous polynomially bounded function realising a
Q-family, using the test-function separation property. -/
theorem function_realisation_unique {f g : ParabolicSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : PolyBounded f) (hgg : PolyBounded g)
    (he : ∀ t, 0 < t → ∀ y, parabolicSemigroup.apply t f y = parabolicSemigroup.apply t g y) :
    f = g := by
  obtain ⟨_, Bf, nf, hBf⟩ := hfg
  obtain ⟨_, Bg, ng, hBg⟩ := hgg
  funext y
  have heq : (fun t => parabolicSemigroup.apply t f y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => parabolicSemigroup.apply t g y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact he t ht y
  exact tendsto_nhds_unique (tendsto_apply_parabolicSemigroup_nhdsGT hf hBf y)
    ((tendsto_apply_parabolicSemigroup_nhdsGT hg hBg y).congr' heq.symm)

end GlobalPhi43.Attachment
