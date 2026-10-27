/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedRadius

/-! Full target-radius range and leaf counts for the augmented iteration,
conditional on the PDE interior estimate. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ContDiff

/-- Monotonicity extends the half-cylinder estimate to every 0<R<1.
The enlarged constant is fixed before R and is independent of boundary data. -/
theorem extend_radius_bound (v : ParabolicSpace → ℝ) {K A : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hb : ∀ R ∈ Ioc (0 : ℝ) (1 / 2), ∀ z ∈ sourceCylinder R,
      |v z| ≤ K * max (1 / R) A) :
    ∀ R ∈ Ioo (0 : ℝ) 1, ∀ z ∈ sourceCylinder R,
      |v z| ≤ (2 * K) * max (1 / R) A := by
  intro R hR z hz
  have hmax0 : 0 ≤ max (1 / R) A := le_max_of_le_right hA
  by_cases hhalf : R ≤ 1 / 2
  · exact (hb R ⟨hR.1, hhalf⟩ z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ 2 * K) hmax0)
  · have hzhalf : z ∈ sourceCylinder (1 / 2) :=
      sourceCylinder_antitone (by norm_num) (le_of_not_ge hhalf) hz
    have hv := hb (1 / 2) (by constructor <;> norm_num) z hzhalf
    norm_num only [one_div_div, div_one] at hv
    have hunit : 1 ≤ 1 / R := (le_div_iff₀ hR.1).2 (by linarith [hR.2])
    have hm : max (2 : ℝ) A ≤ 2 * max (1 / R) A := by
      apply max_le
      · have h := le_max_left (1 / R) A
        linarith
      · have h := le_max_right (1 / R) A
        linarith
    calc
      _ ≤ K * max 2 A := hv
      _ ≤ K * (2 * max (1 / R) A) := mul_le_mul_of_nonneg_left hm hK
      _ = _ := by ring

end GlobalPhi43.Local
