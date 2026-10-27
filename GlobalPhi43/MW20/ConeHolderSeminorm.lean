module

public import GlobalPhi43.MW20.AffineThreePoint
public import GlobalPhi43.MW20.SourceConeEstimate

/-! The coefficient Hölder seminorm and far-pair bound from local coefficient budgets. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- The actual two-sided coefficient Hölder seminorm in the max metric. -/
@[expose] noncomputable def localCoefficientHolderSeminorm
    (ν : ParabolicSpace → Fin 3 → ℝ) (D : Set ParabolicSpace) (α : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ z ∈ D, ⨆ (_ : z ≠ x), ENNReal.ofReal (‖ν x - ν z‖ / pdist x z ^ α)

/-- Far-pair part of the cone argument, with exactly the two source budgets.
This applies to any field satisfying the proved pointwise (2.37) estimate. -/
theorem cone_holder_far_pair (ν : ParabolicSpace → Fin 3 → ℝ)
    {γ r lam A B : ℝ} (hγ : 1 ≤ γ) (hr : 0 < r) (hlam : 0 ≤ lam)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {x z : ParabolicSpace} (hrδ : r ≤ pdist x z)
    (hx : lam * ‖ν x‖ ≤ A * r ^ (γ - 1) + B / r)
    (hz : lam * ‖ν z‖ ≤ A * r ^ (γ - 1) + B / r) :
    lam * ‖ν x - ν z‖ ≤ 2 * (A + B * r ^ (-γ)) * pdist x z ^ (γ - 1) := by
  have hcancel : r ^ (-γ) * r ^ (γ - 1) = 1 / r := by
    rw [← Real.rpow_add hr]
    have he : -γ + (γ - 1) = -1 := by ring
    rw [he, Real.rpow_neg_one, one_div]
  have hid : 2 * (A * r ^ (γ - 1) + B / r) =
      2 * (A + B * r ^ (-γ)) * r ^ (γ - 1) := by
    calc
      _ = 2 * A * r ^ (γ - 1) + 2 * B * (1 / r) := by ring
      _ = _ := by rw [← hcancel]; ring
  have hp : r ^ (γ - 1) ≤ pdist x z ^ (γ - 1) :=
    Real.rpow_le_rpow hr.le hrδ (sub_nonneg.mpr hγ)
  calc
    lam * ‖ν x - ν z‖ ≤ lam * (‖ν x‖ + ‖ν z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hlam
    _ ≤ 2 * (A * r ^ (γ - 1) + B / r) := by linarith
    _ = 2 * (A + B * r ^ (-γ)) * r ^ (γ - 1) := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end GlobalPhi43.MW20
