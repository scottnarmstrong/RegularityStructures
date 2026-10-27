module

public import GlobalPhi43.Attachment.PositiveTreeCoefficients
public import GlobalPhi43.Attachment.TestGeometry
public import GlobalPhi43.Attachment.Pairing
public import Phi43.LiftBounds.Norm
import Mathlib.Tactic.Linarith

/-! Positive-tree increments from the actual compact model norm, with metric factor four. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local Set

/-- The metric comparison costs at most four for every exponent in [0,1]. -/
theorem parabolicNorm_rpow_le_four_pdist {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : ParabolicSpace) : parabolicNorm (y - x) ^ α ≤ 4 * pdist x y ^ α := by
  have hb : parabolicNorm (y - x) ≤ 4 * pdist x y := by
    simpa only [pdist_symm y x] using parabolicNorm_le_four_pdist y x
  calc _ ≤ (4 * pdist x y) ^ α := Real.rpow_le_rpow (parabolicNorm_nonneg _) hb hα
    _ = (4 : ℝ) ^ α * pdist x y ^ α := Real.mul_rpow (by norm_num) (pdist_nonneg _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num) hα1) (Real.rpow_nonneg (pdist_nonneg _ _) _)

variable {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- Both positive increments use the same compact model norm, including zero norm. -/
theorem positive_tree_increments (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    {S : Set ParabolicSpace} (hS : IsCompact S) {x y : ParabolicSpace}
    (hx : x ∈ S) (hy : y ∈ S) :
    let M := (Z.normOn (gamma κ) S).toReal
    (|treeY N f (C₁ C) (spaceTimeProj y) - treeY N f (C₁ C) (spaceTimeProj x)| ≤
      M * parabolicNorm (y - x) ^ (1 - 2 * κ.val)) ∧
    (M * parabolicNorm (y - x) ^ (1 - 2 * κ.val) ≤
      4 * M * pdist x y ^ (1 - 2 * κ.val)) ∧
    (|treeZ N f (C₁ C) (spaceTimeProj y) - treeZ N f (C₁ C) (spaceTimeProj x)| ≤
      M * parabolicNorm (y - x) ^ (1 / 2 - 3 * κ.val)) ∧
    (M * parabolicNorm (y - x) ^ (1 / 2 - 3 * κ.val) ≤
      4 * M * pdist x y ^ (1 / 2 - 3 * κ.val)) := by
  have hfin : Z.normOn (gamma κ) S ≠ ⊤ := by
    obtain ⟨_, _, hm⟩ := hZ
    exact hm.2.2.1 S hS
  let M := (Z.normOn (gamma κ) S).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hG := LiftBounds.gammaBoundOn_of_normOn_le Z hM (le_of_eq (ENNReal.ofReal_toReal hfin).symm)
  have hY : 0 < 1 - 2 * κ.val := by linarith [κ.property.2]
  have hZt : 0 < 1 / 2 - 3 * κ.val := by linarith [κ.property.2]
  have hYγ : homogeneity κ .iPsiSq < gamma κ := by
    simp only [homogeneity, gamma]; linarith [κ.property.1]
  have hZγ : homogeneity κ .iPsiCube < gamma κ := by
    simp only [homogeneity, gamma]; linarith [κ.property.1]
  have hGY := hG .iPsiSq .one hYγ hY x hx y hy
  have hGZ := hG .iPsiCube .one hZγ hZt x hx y hy
  rw [gamma_treeY_coefficient hf hg hZ] at hGY
  rw [gamma_treeZ_coefficient hf hg hZ] at hGZ
  have hmetric (α : ℝ) (ha : 0 ≤ α) (ha1 : α ≤ 1) :
      M * parabolicNorm (y - x) ^ α ≤ 4 * M * pdist x y ^ α := by
    have h := mul_le_mul_of_nonneg_left (parabolicNorm_rpow_le_four_pdist ha ha1 x y) hM
    nlinarith
  refine ⟨?_, hmetric _ hY.le (by linarith [κ.property.1]), ?_,
    hmetric _ hZt.le (by linarith [κ.property.1])⟩
  · simpa only [M, phi43RegularityStructure, homogeneity, sub_zero, parabolicSemigroup] using hGY
  · simpa only [M, phi43RegularityStructure, homogeneity, sub_zero, parabolicSemigroup] using hGZ

/-- The exact radius-three max-metric enlargement used by the source seminorm node. -/
theorem positive_tree_increments_on_enlargement (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    {D : Set ParabolicSpace} (hD : IsCompact D) {x y : ParabolicSpace}
    (hx : x ∈ {y | ∃ z ∈ D, pdist z y ≤ 3})
    (hy : y ∈ {y | ∃ z ∈ D, pdist z y ≤ 3}) :
    let M := (Z.normOn (gamma κ) {y | ∃ z ∈ D, pdist z y ≤ 3}).toReal
    (|treeY N f (C₁ C) (spaceTimeProj y) - treeY N f (C₁ C) (spaceTimeProj x)| ≤
      M * parabolicNorm (y - x) ^ (1 - 2 * κ.val)) ∧
    (M * parabolicNorm (y - x) ^ (1 - 2 * κ.val) ≤
      4 * M * pdist x y ^ (1 - 2 * κ.val)) ∧
    (|treeZ N f (C₁ C) (spaceTimeProj y) - treeZ N f (C₁ C) (spaceTimeProj x)| ≤
      M * parabolicNorm (y - x) ^ (1 / 2 - 3 * κ.val)) ∧
    (M * parabolicNorm (y - x) ^ (1 / 2 - 3 * κ.val) ≤
      4 * M * pdist x y ^ (1 / 2 - 3 * κ.val)) :=
  positive_tree_increments hf hg hZ (isCompact_parabolic_enlargement hD (by norm_num)) hx hy

end GlobalPhi43.Attachment
