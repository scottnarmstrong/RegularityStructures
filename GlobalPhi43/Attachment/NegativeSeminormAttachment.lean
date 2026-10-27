module

public import GlobalPhi43.Attachment.OrdinaryTreeSeminorms
public import GlobalPhi43.Attachment.RecenteredScalarSeminorms
public import GlobalPhi43.Attachment.CoordinateTreeSeminorms

/-! Negative-tree seminorm bounds from the model norm.
Positive-tree seminorm bounds use the corresponding increment identities. -/

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- All seven actual source seminorms share one constant chosen before every
noise, model, renormalisation parameter and compact base domain. -/
theorem negative_seminorm_attachment (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ (S : Set ParabolicSpace), IsCompact S →
      let J := fun y => treeJ N f (spaceTimeProj y)
      let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
      let W := fun y => treeW N f (C₁ C) (spaceTimeProj y)
      let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
      let Zt := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
      let B := ENNReal.ofReal K * (1+Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-(1/2)-κ.1) J ≤ B ∧
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-1-2*κ.1) V ≤ B ∧
      negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S (-(3/2)-3*κ.1) W ≤ B ∧
      recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S κ.1 V ≤ B ∧
      recenteredASeminorm (mw20TestingKernel Φ hΦ) S κ.1 Y V (C₂ C) ≤ B ∧
      recenteredBSeminorm (mw20TestingKernel Φ hΦ) S κ.1 Zt J ≤ B ∧
      recenteredDSeminorm (mw20TestingKernel Φ hΦ) S κ.1 Zt V J (C₂ C) ≤ B := by
  obtain ⟨K1,hK1,h1⟩ := ordinary_tree_seminorms N κ Φ hΦ
  obtain ⟨K2,hK2,h2⟩ := recentered_scalar_seminorms N κ Φ hΦ
  obtain ⟨K3,hK3,h3⟩ := coordinate_tree_seminorm N κ Φ hΦ
  refine ⟨K1+K2+K3,by positivity,?_⟩
  intro f C Z hf hg hZ S hS
  obtain ⟨hJ,hV,hW⟩ := h1 f C Z hf hg hZ S hS
  obtain ⟨hA,hB,hD⟩ := h2 f C Z hf hg hZ S hS
  have hX := h3 f C Z hf hg hZ S hS
  have hm1 : ENNReal.ofReal K1 ≤ ENNReal.ofReal (K1+K2+K3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hm2 : ENNReal.ofReal K2 ≤ ENNReal.ofReal (K1+K2+K3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hm3 : ENNReal.ofReal K3 ≤ ENNReal.ofReal (K1+K2+K3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  exact ⟨hJ.trans (mul_le_mul_left hm1 _), hV.trans (mul_le_mul_left hm1 _),
    hW.trans (mul_le_mul_left hm1 _), hX.trans (mul_le_mul_left hm3 _),
    hA.trans (mul_le_mul_left hm2 _), hB.trans (mul_le_mul_left hm2 _),
    hD.trans (mul_le_mul_left hm2 _)⟩

end GlobalPhi43.Attachment
