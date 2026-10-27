module

public import GlobalPhi43.Attachment.NegativeTreeSeminorms

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Clause (i): the actual ordinary J,V,W source norms, including scale one,
with one uniform cubic model allowance and the exact radius-three domain. -/
theorem ordinary_tree_seminorms (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ (S : Set ParabolicSpace), IsCompact S →
      let B := ENNReal.ofReal K * (1+Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-(1/2)-κ.1)
          (fun y => treeJ N f (spaceTimeProj y)) ≤ B ∧
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-1-2*κ.1)
          (fun y => treeV N f (C₁ C) (spaceTimeProj y)) ≤ B ∧
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-(3/2)-3*κ.1)
          (fun y => treeW N f (C₁ C) (spaceTimeProj y)) ≤ B := by
  obtain ⟨K,hK,hbound⟩ := source_negative_tree_seminorm N κ Φ hΦ
  refine ⟨K,hK,?_⟩
  intro f C Z hf hg hZ S hS
  have hτ (τ : Symbol) (hm : τ ∈ fMinus) (hX : ∀ i, τ ≠ .psiSqX i) :=
    hbound f C Z hf hg hZ S hS (Ioc 0 1) Subset.rfl τ hm hX
  refine ⟨?_,?_,?_⟩
  · simpa only [negativeTreeSeminorm, homogeneity, neg_div, hairerTreeField, treeJ] using
      hτ .psi (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)
  · simpa only [negativeTreeSeminorm, homogeneity, neg_div, hairerTreeField, hairerTreePsiSq,
      treeV,treeJ] using
      hτ .psiSq (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)
  · simpa only [negativeTreeSeminorm, homogeneity, neg_div, hairerTreeField, hairerTreePsiCube,
      treeW,treeJ] using
      hτ .psiCube (by simp [mem_fMinus_iff_isFMinus,isFMinus]) (by intro i; simp)

end GlobalPhi43.Attachment
