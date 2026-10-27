module

public import GlobalPhi43.Attachment.CoverLocalData
public import GlobalPhi43.Attachment.CoverNormDomains

/-! Actual nine-tree norm transport for the concrete cover application.
Closed/open negative test cutoffs are retained before comparison with scale one. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal

namespace GlobalPhi43.Attachment

/-- The actual nine normalized source norms of the scaled local-data tuple.
V/W are written in their exactly equal transported polynomial form. -/
@[expose] def scaledAttachmentTreeSeminorm (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : SpaceTime → ℝ) (C : RenormalisationConstants) (b : ParabolicSpace) (l : ℝ)
    (D : Set ParabolicSpace) (τ : LocalTree) : ℝ≥0∞ :=
  let J := fun y => treeJ N f (spaceTimeProj y)
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  let W := fun y => treeW N f (C₁ C) (spaceTimeProj y)
  let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
  let Z := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  let K := mw20TestingKernel Φ hΦ
  match τ with
  | .J => negativeTreeSeminorm K D (-1/2-κ.1) (parabolicPullback l J b l)
  | .V => negativeTreeSeminorm K D (-1-2*κ.1) (parabolicPullback (l^2) V b l)
  | .W => negativeTreeSeminorm K D (-3/2-3*κ.1) (parabolicPullback (l^3) W b l)
  | .Y => scalarHolderSeminorm (parabolicPullback 1 Y b l) D (1-2*κ.1)
  | .Z => scalarHolderSeminorm (parabolicPullback l Z b l) D (1/2-3*κ.1)
  | .XV => recenteredXVSeminorm K D κ.1 (parabolicPullback (l^2) V b l)
  | .A => recenteredASeminorm K D κ.1 (parabolicPullback 1 Y b l)
      (parabolicPullback (l^2) V b l) (l^2*C₂ C)
  | .B => recenteredBSeminorm K D κ.1 (parabolicPullback l Z b l) (parabolicPullback l J b l)
  | .D => recenteredDSeminorm K D κ.1 (parabolicPullback l Z b l)
      (parabolicPullback (l^2) V b l) (parabolicPullback l J b l) (l^2*C₂ C)

/-- The source degree n*(1/2-kappa) is retained for EVERY entry, including
positive Y/Z, vector XV and the complete signed A/B/D counterterms. -/
theorem scaledAttachmentTreeSeminorm_le (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (b : ParabolicSpace) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1)
    (D : Set ParabolicSpace) (τ : LocalTree) :
    scaledAttachmentTreeSeminorm N κ Φ hΦ f C b l D τ ≤
      ENNReal.ofReal (l^(τ.degree κ.1)) *
        attachmentTreeSeminorm N κ Φ hΦ f C (parabolicMap b l '' D) τ := by
  let J := fun y => treeJ N f (spaceTimeProj y)
  let V := fun y => treeV N f (C₁ C) (spaceTimeProj y)
  let W := fun y => treeW N f (C₁ C) (spaceTimeProj y)
  let Y := fun y => treeY N f (C₁ C) (spaceTimeProj y)
  let Z := fun y => treeZ N f (C₁ C) (spaceTimeProj y)
  let S := parabolicMap b l '' D
  let K := mw20TestingKernel Φ hΦ
  have ho := ordinary_tree_scaling Φ hΦ J V W b hl D κ.1
  have hp := positive_tree_scaling Y Z b hl D κ.1
  have hV : Continuous V := (continuous_treeV hf _).comp continuous_spaceTimeProj
  have hclosed (α : ℝ) (G : ParabolicSpace → ParabolicSpace → ℝ) :=
    localTestSeminorm_Ioc_scale_le K S hl1 α G
  have hopen (α : ℝ) (G : ParabolicSpace → ParabolicSpace → ℝ) :=
    localTestSeminorm_Ioo_scale_le K S hl1 α G
  have hy : ENNReal.ofReal (l^(1-2*κ.1)) = ENNReal.ofReal (l^(2*(1/2-κ.1))) :=
    congrArg (fun r : ℝ => ENNReal.ofReal (l^r)) (by ring)
  have hz : ENNReal.ofReal (l^(3/2-3*κ.1)) = ENNReal.ofReal (l^(3*(1/2-κ.1))) :=
    congrArg (fun r : ℝ => ENNReal.ofReal (l^r)) (by ring)
  rw [hy] at hp
  rw [hz] at hp
  cases τ
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_one, one_mul] using
      ho.1.le.trans (mul_le_mul_right (hclosed _ (fun _ => J)) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      ho.2.1.le.trans (mul_le_mul_right (hclosed _ (fun _ => V)) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      ho.2.2.le.trans (mul_le_mul_right (hclosed _ (fun _ => W)) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using hp.1.le
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using hp.2.le
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      (recenteredXV_scaling Φ hΦ V hV b hl D κ.1).le.trans
        (mul_le_mul_right (coordinateTree_truncated_le K S hl1 κ.1 V) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      (recenteredA_scaling Φ hΦ Y V (C₂ C) b hl D κ.1).le.trans
        (mul_le_mul_right (hopen _ (fun x y => (Y y-Y x)*V y-C₂ C)) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      (recenteredB_scaling Φ hΦ Z J b hl D κ.1).le.trans
        (mul_le_mul_right (hopen _ (fun x y => (Z y-Z x)*J y)) _)
  · simpa only [scaledAttachmentTreeSeminorm, attachmentTreeSeminorm,
      negativeTreeSeminorm, recenteredASeminorm, recenteredBSeminorm, recenteredDSeminorm,
      J, V, W, Y, Z, S, K, neg_div,
      LocalTree.degree, LocalTree.leaves, Nat.cast_ofNat] using
      (recenteredD_scaling Φ hΦ Z V J (C₂ C) b hl D κ.1).le.trans
        (mul_le_mul_right (hopen _ (fun x y => (Z y-Z x)*V y-3*C₂ C*J y)) _)

end GlobalPhi43.Attachment
