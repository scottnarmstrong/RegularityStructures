module

public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.MW20.ConeHolderSeminorm

/-! Literal norm extractions for the optimal coefficient selected from the
source expansion. These do not estimate that norm by any Schauder adapter. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The affine source norm controls the remainder at the actual selected
spatial derivative, with no separately supplied optimality premise. -/
theorem source_affine_norm_remainder (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ N : ℝ} (hγ : 1 < γ) (hN : 0 ≤ N)
    (hnorm : localAffineSeminorm (sourceExpansion v Y Z) D γ ≤ ENNReal.ofReal N)
    {a b : ParabolicSpace} (ha : a ∈ D) (hb : b ∈ D) (hne : b ≠ a) :
    |Local.expansion v Y Z a b - ∑ i, sourceAffineCoefficient v Y Z a i * (b.2 i - a.2 i)| ≤
      N * pdist a b ^ γ :=
  localAffineSeminorm_remainder_bound _ (sourceExpansion_contDiff v Y Z hv hY hZ) D hD
    hγ hN hnorm ha hb hne

/-- Componentwise coefficient increments from the actual vector Holder norm. -/
theorem source_coefficient_holder_component_bound
    (ν : ParabolicSpace → Fin 3 → ℝ) (D : Set ParabolicSpace) (α : ℝ)
    {N : ℝ} (hN : 0 ≤ N)
    (hnorm : localCoefficientHolderSeminorm ν D α ≤ ENNReal.ofReal N)
    {a b : ParabolicSpace} (ha : a ∈ D) (hb : b ∈ D) (hne : b ≠ a) (i : Fin 3) :
    |ν a i - ν b i| ≤ N * pdist a b ^ α := by
  have hh : ∀ a ∈ D, ∀ b ∈ D, ∀ (_ : b ≠ a),
      ENNReal.ofReal (‖ν a - ν b‖ / pdist a b ^ α) ≤ ENNReal.ofReal N := by
    simpa only [localCoefficientHolderSeminorm, iSup_le_iff] using hnorm
  have hr := (ENNReal.ofReal_le_ofReal_iff hN).mp (hh a ha b hb hne)
  have hnormab := (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).mp hr
  exact (norm_le_pi_norm (ν a - ν b) i).trans hnormab

end GlobalPhi43.MW20
