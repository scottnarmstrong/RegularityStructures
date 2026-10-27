module

public import GlobalPhi43.Attachment.NegativeTreeSeminorms
public import GlobalPhi43.Attachment.RecenteredTreeIdentities

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Scalar part of clause (ii): literal A,B,D seminorms with the source
counterterms, strict upper endpoint, and one uniform cubic model allowance. -/
theorem recentered_scalar_seminorms (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ (S : Set ParabolicSpace), IsCompact S →
      let J := fun y => treeJ N f (spaceTimeProj y)
      let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
      let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
      let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
      let B := ENNReal.ofReal K * (1+Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3
      recenteredASeminorm (mw20TestingKernel Φ hΦ) S κ.1 Y V (C₂ C) ≤ B ∧
      recenteredBSeminorm (mw20TestingKernel Φ hΦ) S κ.1 Zt J ≤ B ∧
      recenteredDSeminorm (mw20TestingKernel Φ hΦ) S κ.1 Zt V J (C₂ C) ≤ B := by
  obtain ⟨K,hK,hbound⟩ := source_negative_tree_seminorm N κ Φ hΦ
  refine ⟨K,hK,?_⟩
  intro f C Z hf hg hZ S hS
  have hτ (τ : Symbol) (hm : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) :=
    hbound f C Z hf hg hZ S hS (Ioo 0 1) (fun _ ht => ⟨ht.1,ht.2.le⟩) τ hm hX
  refine ⟨?_,?_,?_⟩
  · have hh := hτ .iPsiSqPsiSq (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)
    simpa only [recenteredASeminorm, homogeneity, source_A_eq N f hf C] using hh
  · have hh := hτ .iPsiCubePsi (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)
    simpa only [recenteredBSeminorm, homogeneity, source_B_eq N f hf C] using hh
  · have hh := hτ .iPsiCubePsiSq (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)
    simpa only [recenteredDSeminorm, homogeneity, neg_div, source_D_eq N f hf C] using hh

end GlobalPhi43.Attachment
