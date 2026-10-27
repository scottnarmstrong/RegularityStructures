module

public import GlobalPhi43.Attachment.PositiveTreeIncrements
public import GlobalPhi43.Attachment.Model
public import GlobalPhi43.MW20.ScalarHolderSeminorm

/-! Positive clause (iii) of the attachment seminorm lemma, for the actual attached trees. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local Set

variable {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- Full compact-pair source seminorm bounds, with no radius truncation or new norm. -/
theorem positive_tree_seminorm_bounds (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    {D : Set ParabolicSpace} (hD : IsCompact D) :
    let M := (Z.normOn (gamma κ) {y | ∃ z ∈ D, pdist z y ≤ 3}).toReal
    (MW20.scalarHolderSeminorm (fun z => treeY N f (C₁ C) (spaceTimeProj z)) D
      (1 - 2 * κ.val) ≤ ENNReal.ofReal (4 * M)) ∧
    (MW20.scalarHolderSeminorm (fun z => treeZ N f (C₁ C) (spaceTimeProj z)) D
      (1 / 2 - 3 * κ.val) ≤ ENNReal.ofReal (4 * M)) := by
  have hin (x : ParabolicSpace) (hx : x ∈ D) : x ∈ {y | ∃ z ∈ D, pdist z y ≤ 3} := by
    exact ⟨x, hx, by simp only [pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self]; norm_num⟩
  constructor
  · simp only [MW20.scalarHolderSeminorm, iSup_le_iff]
    intro x hx y hy hne
    have hb := positive_tree_increments_on_enlargement hf hg hZ hD (hin x hx) (hin y hy)
    exact ENNReal.ofReal_le_ofReal
      ((div_le_iff₀ (Real.rpow_pos_of_pos (MW20.pdist_pos_of_ne hne) _)).2
        (hb.1.trans hb.2.1))
  · simp only [MW20.scalarHolderSeminorm, iSup_le_iff]
    intro x hx y hy hne
    have hb := positive_tree_increments_on_enlargement hf hg hZ hD (hin x hx) (hin y hy)
    exact ENNReal.ofReal_le_ofReal
      ((div_le_iff₀ (Real.rpow_pos_of_pos (MW20.pdist_pos_of_ne hne) _)).2
        (hb.2.2.1.trans hb.2.2.2))

end GlobalPhi43.Attachment
