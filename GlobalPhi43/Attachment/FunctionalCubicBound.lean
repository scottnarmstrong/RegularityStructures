module

public import GlobalPhi43.Attachment.TreeFunctional
public import GlobalPhi43.Attachment.FunctionalPowerBound

/-! Seventh-power bounds for the tree functional, assuming cubic bounds
for the nine trees. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20

/-- Actual tree/defect cubic bounds imply the exact fixed seventh-power allowance.
The tree and defect cubic bounds are explicit hypotheses. -/
theorem attachmentFunctional_le_of_cubic (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (htree : ∀ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f C S τ ≤
      ENNReal.ofReal (A * (1 + R) ^ 3))
    (hdefect : ∀ i : Fin 3, localScalarSup (defectField N f C i) S ≤
      ENNReal.ofReal (A * (1 + R) ^ 3)) :
    attachmentFunctional N κ Φ hΦ f C S ≤
      ENNReal.ofReal ((1 + A) ^ (((1/2 : ℝ) - κ.1)⁻¹) * (1 + R) ^ (7 : ℝ)) := by
  have hb : 0 < (1/2 : ℝ) - κ.1 := by linarith only [κ.2.2]
  have hp (τ : LocalTree) : (1/2 : ℝ) - κ.1 ≤ τ.degree κ.1 := by
    have hn : (1 : ℝ) ≤ (τ.leaves : ℝ) := by exact_mod_cast Nat.succ_le_of_lt τ.leaves_pos
    unfold LocalTree.degree
    nlinarith only [hn, hb]
  have htreeRoot : (⨆ τ : LocalTree, attachmentTreeSeminorm N κ Φ hΦ f C S τ ^ (τ.degree κ.1)⁻¹) ≤
      ENNReal.ofReal ((1 + A) ^ (((1/2 : ℝ) - κ.1)⁻¹) * (1 + R) ^ (7 : ℝ)) :=
    iSup_le fun τ => cubic_root_ENNReal_le_seventh κ hA hR (hp τ) (htree τ)
  have h3 : (1/2 : ℝ) - κ.1 ≤ 3 := by linarith only [κ.2.1]
  have h2 : (1/2 : ℝ) - κ.1 ≤ 2 := by linarith only [κ.2.1]
  have he0 := cubic_root_ENNReal_le_seventh κ hA hR h3 (hdefect 0)
  have he1 := cubic_root_ENNReal_le_seventh κ hA hR h2 (hdefect 1)
  have he2 := cubic_root_ENNReal_le_seventh κ hA hR h3 (hdefect 2)
  unfold attachmentFunctional
  exact max_le htreeRoot (max_le (by simpa only [one_div] using he0)
    (max_le (by simpa only [one_div] using he1) (by simpa only [one_div] using he2)))

end GlobalPhi43.Attachment
