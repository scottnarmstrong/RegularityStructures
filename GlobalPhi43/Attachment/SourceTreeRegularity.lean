module

public import GlobalPhi43.Attachment.NegativeRealisations
public import Phi43.Structure.RenormalisedExtensionTensorH0

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43

/-- The literal source tree fields inherit polynomial growth from the canonical
smooth realisations; this is qualitative, without a new quantitative budget. -/
theorem source_tree_regular {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    (τ : Symbol) (hτ : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) (x : ParabolicSpace) :
    let g := fun y => hairerTreeField N (fun _ : Unit => f) (C₁ C) (C₂ C)
      (spaceTimeProj x) () τ (spaceTimeProj y)
    Continuous g ∧ PolyBounded g := by
  obtain ⟨noise,hn,_,_⟩ := regPi_fMinus hZ
  obtain ⟨Cg,q,hgr⟩ := hg
  have hn' := noise_zeta_eq hn
  have hgr' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg*(1+parabolicNorm z)^q := by
    have he := funext hn'
    rw [he]
    exact hgr
  have hpoly := canonicalNoise_polyBounded_of_derivatives noise Cg q hgr'
  have hs := (renormalisedExtensionPi_smooth N (κ := κ) noise C x (basis τ)).continuous
  have hp := renormalisedExtensionPi_growth N (κ := κ) noise hpoly C x (basis τ)
  have hF : IsHairerF0 τ := by
    rw [mem_fMinus_iff_isFMinus] at hτ
    cases τ <;> simp only [isFMinus, IsHairerF0] at hτ ⊢
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ noise C x τ (Or.inl hF),
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_eq_treeField
      (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf hτ hX] at hs hp
  exact ⟨hs,hp⟩

/-- Qualitative regularity of every literal XV coordinate realisation. -/
theorem source_XV_regular {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    (x : ParabolicSpace) (i : Fin 3) :
    let g := fun y : ParabolicSpace => (y.2 i-x.2 i)*treeV N f (C₁ C) (spaceTimeProj y)
    Continuous g ∧ PolyBounded g := by
  obtain ⟨noise,hn,_,_⟩ := regPi_fMinus hZ
  obtain ⟨Cg,q,hgr⟩ := hg
  have hn' := noise_zeta_eq hn
  have hgr' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg*(1+parabolicNorm z)^q := by
    have he := funext hn'
    rw [he]
    exact hgr
  have hpoly := canonicalNoise_polyBounded_of_derivatives noise Cg q hgr'
  have hs := (renormalisedExtensionPi_smooth N (κ := κ) noise C x (basis (.psiSqX i))).continuous
  have hp := renormalisedExtensionPi_growth N (κ := κ) noise hpoly C x (basis (.psiSqX i))
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ noise C x (.psiSqX i)
      (Or.inl (by simp [IsHairerF0])),
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiSqX_eq
      (ξ := fun _ : Unit => f) (ω := ()) x C hn' hf i] at hs hp
  have he : (fun y : ParabolicSpace => hairerTreePsiSq N (fun _ : Unit => f)
      (C₁ C) () (spaceTimeProj y)*(y.2 i-x.2 i)) =
      (fun y : ParabolicSpace => (y.2 i-x.2 i)*treeV N f (C₁ C) (spaceTimeProj y)) := by
    funext y
    exact mul_comm _ _
  rw [he] at hs hp
  exact ⟨hs,hp⟩

end GlobalPhi43.Attachment
