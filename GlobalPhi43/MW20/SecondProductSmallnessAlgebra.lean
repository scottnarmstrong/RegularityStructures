module

public import GlobalPhi43.MW20.SecondProductBudget

/-!
# The parent tree substitutions in MW20 (4.3)
-/

public section

namespace GlobalPhi43.MW20

/-- All four second-product tree contributions contain exactly one factor c.
No product of tree allowances or counterterm-size estimate is introduced. -/
theorem second_product_parent_smallness {T ε M Hv HU Hν N c : ℝ}
    (hM : 0 ≤ M) (hsmall : ε < 1 / 14) :
    T ^ (1 / 2 - 7 * ε) *
        (Hv * (c * M ^ (2 - 4 * ε)) + HU * (c * M ^ (1 - 2 * ε)) +
          Hν * (c * M ^ (1 - 2 * ε))) +
      (c * M ^ (5 / 2 - 5 * ε)) * T ^ (-(1 / 2) - 5 * ε) +
      T ^ (-4 * ε) * M * (c * M ^ (2 - 4 * ε)) +
      N * (c * M ^ (1 - 2 * ε)) * T ^ (-2 * ε) =
    c * (T ^ (1 / 2 - 7 * ε) *
        (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
      M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
      T ^ (-4 * ε) * M ^ (3 - 4 * ε) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)) := by
  have hm : M * M ^ (2 - 4 * ε) = M ^ (3 - 4 * ε) := by
    calc
      _ = M ^ (1 : ℝ) * M ^ (2 - 4 * ε) := by rw [Real.rpow_one]
      _ = M ^ (1 + (2 - 4 * ε)) :=
        (Real.rpow_add' hM (by linarith : 1 + (2 - 4 * ε) ≠ 0)).symm
      _ = _ := by congr 1; ring
  calc
    _ = c * (T ^ (1 / 2 - 7 * ε) *
        (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
      M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
      T ^ (-4 * ε) * (M * M ^ (2 - 4 * ε)) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)) := by ring
    _ = _ := by rw [hm]

end GlobalPhi43.MW20
