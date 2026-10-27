module

public import Phi43.Structure.Symbols
import Mathlib.Tactic.Linarith

/-! The finite homogeneity comparison for the negative symbols.
This checks the full basis, including symbols below the chosen symbol. -/

public section

namespace GlobalPhi43.Attachment

open RegularityStructures.Phi43

/-- The raw noise has minimum homogeneity in the finite structure. -/
theorem noise_homogeneity_le (κ : Kappa) (τ : Symbol) :
    -(5 / 2 : ℝ) - κ.1 ≤ homogeneity κ τ := by
  have hpos := κ.2.1
  have hsmall := κ.2.2
  cases τ <;> simp only [homogeneity] <;> linarith

/-- Every possible exponent in the local model bound is strictly above minus four. -/
theorem homogeneity_gt_neg_four (κ : Kappa) (τ : Symbol) :
    -(4 : ℝ) < homogeneity κ τ := by
  have hsmall := κ.2.2
  have hmin := noise_homogeneity_le κ τ
  linarith

end GlobalPhi43.Attachment
