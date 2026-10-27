module

public import GlobalPhi43.Attachment.NegativeSeminormAttachment
public import GlobalPhi43.Attachment.PositiveTreeSeminorms
public import GlobalPhi43.Attachment.FunctionalCubicBound
public import GlobalPhi43.Attachment.DefectSupBounds

/-! Uniform seventh-power bound for the actual nine-tree attachment functional. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Actual model norms are monotone under enlargement of the source base set. -/
theorem attachment_normOn_mono {κ : Kappa}
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    {S T : Set ParabolicSpace} (h : S ⊆ T) : Z.normOn (gamma κ) S ≤ Z.normOn (gamma κ) T := by
  unfold Model.normOn Model.piNormOn Model.gammaNormOn
  apply add_le_add
  · exact le_iInf₂ fun B hB => iInf₂_le B fun i hi t ht x hx => hB i hi t ht x (h hx)
  · exact le_iInf₂ fun B hB => iInf₂_le B fun i j hi hj x hx y hy =>
      hB i j hi hj x (h hx) y (h hy)

/-- The tree functional bound, with one constant before all noise/model/domain data. -/
theorem attachment_functional_bound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S →
      attachmentFunctional N κ Φ hΦ f C S ≤ ENNReal.ofReal (c *
        (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4}).toReal) ^ (7 : ℝ)) := by
  obtain ⟨K, hK, hneg⟩ := negative_seminorm_attachment N κ Φ hΦ
  obtain ⟨d, hd, hdef⟩ := defect_sup_bounds N κ
  let A := K + 4 + d
  refine ⟨(1 + A) ^ (((1/2 : ℝ) - κ.1)⁻¹), Real.rpow_pos_of_pos (by dsimp [A]; positivity) _, ?_⟩
  intro f C Z hf hg hZ S hS
  let M3 := (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal
  let M4 := (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4}).toReal
  have hfin (r : ℝ) (hr : 0 ≤ r) : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ r} ≠ ⊤ := by
    obtain ⟨noise, hn, hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement hS hr)
  have h34 : M3 ≤ M4 := ENNReal.toReal_mono (hfin 4 (by norm_num))
    (attachment_normOn_mono Z (by rintro y ⟨z, hz, he⟩; exact ⟨z, hz, by linarith⟩))
  have hM3 : 0 ≤ M3 := ENNReal.toReal_nonneg
  have hM4 : 0 ≤ M4 := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnegBudget : ENNReal.ofReal K *
      (1 + Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3 ≤
      ENNReal.ofReal (A * (1 + M4)^3) := by
    have he : ENNReal.ofReal K *
        (1 + Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3 =
        ENNReal.ofReal (K * (1 + M3)^3) := by
      rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_pow,
        ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) hM3, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal (hfin 3 (by norm_num))]
      positivity
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    have hKA : K ≤ A := by dsimp [A]; linarith
    gcongr
  have hposBudget : ENNReal.ofReal (4*M3) ≤ ENNReal.ofReal (A*(1+M4)^3) := by
    apply ENNReal.ofReal_le_ofReal
    have h4A : 4 ≤ A := by dsimp [A]; linarith
    have hcube : M4 ≤ (1+M4)^3 := by nlinarith [sq_nonneg M4]
    calc 4*M3 ≤ 4*M4 := by gcongr
         _ ≤ 4*(1+M4)^3 := by gcongr
         _ ≤ A*(1+M4)^3 := by gcongr
  obtain ⟨hJ,hV,hW,hXV,hAA,hB,hD⟩ := hneg f C Z hf hg hZ S hS
  obtain ⟨hY,hZt⟩ := positive_tree_seminorm_bounds hf hg hZ hS
  apply attachmentFunctional_le_of_cubic N κ Φ hΦ f C S hA hM4
  · intro τ
    cases τ with
    | J => exact hJ.trans hnegBudget
    | V => exact hV.trans hnegBudget
    | W => exact hW.trans hnegBudget
    | Y => exact hY.trans hposBudget
    | Z => exact hZt.trans hposBudget
    | XV => exact hXV.trans hnegBudget
    | A => exact hAA.trans hnegBudget
    | B => exact hB.trans hnegBudget
    | D => exact hD.trans hnegBudget
  · intro i
    apply (hdef f C Z hf hg hZ S hS i).trans
    apply ENNReal.ofReal_le_ofReal
    have hdA : d ≤ A := by dsimp [A]; linarith
    change d*(1+M4)^3 ≤ A*(1+M4)^3
    gcongr

end GlobalPhi43.Attachment
