module

public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.ConeHolderSeminorm

/-! Comparisons between pointwise estimates and the source seminorms
in the coefficient and product bounds. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- A literal radius-local remainder estimate bounds the actual sup-inf-sup
seminorm. No attainment or smoothness assumption is needed for this direction. -/
theorem radiusAffineSeminorm_le_of_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (ν : ParabolicSpace → Fin 3 → ℝ) (γ L A : ℝ)
    (hbound : ∀ x ∈ D, ∀ y ∈ D, pdist x y ≤ L → y ≠ x →
      |U (x, y) - ∑ j, ν x j * (y.2 j - x.2 j)| ≤ A * pdist x y ^ γ) :
    radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal A := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply (iInf_le (fun a => radiusAffineRemainderSeminorm U D γ L x a) (ν x)).trans
  change affineRemainderSeminorm U (D ∩ {y | pdist x y ≤ L}) γ x (ν x) ≤ ENNReal.ofReal A
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hne
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).2
    (hbound x hx y hy.1 hy.2 hne)

/-- Restrict the actual coefficient Holder norm to a testing domain. -/
theorem localCoefficientHolderSeminorm_mono
    (ν : ParabolicSpace → Fin 3 → ℝ) {D E : Set ParabolicSpace} (α : ℝ) (hDE : D ⊆ E) :
    localCoefficientHolderSeminorm ν D α ≤ localCoefficientHolderSeminorm ν E α := by
  have hall : ∀ x ∈ E, ∀ z ∈ E, ∀ (_ : z ≠ x),
      ENNReal.ofReal (‖ν x - ν z‖ / pdist x z ^ α) ≤ localCoefficientHolderSeminorm ν E α := by
    simpa only [localCoefficientHolderSeminorm, iSup_le_iff] using
      (le_rfl : localCoefficientHolderSeminorm ν E α ≤ localCoefficientHolderSeminorm ν E α)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply iSup_le
  intro hne
  exact hall x (hDE hx) z (hDE hz) hne

end GlobalPhi43.MW20
