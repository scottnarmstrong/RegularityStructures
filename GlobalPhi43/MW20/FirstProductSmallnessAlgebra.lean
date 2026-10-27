module

public import GlobalPhi43.MW20.FirstProductBudget

/-!
# The exact parent tree substitutions in MW20 (4.2)
-/

public section

namespace GlobalPhi43.MW20

/-- Parent (4.1) in the four Lemma 2.9 budgets. The c² term is weakened
only to c, preserving all parent powers and the single smallness allowance. -/
theorem first_product_parent_smallness {T ε M H Hv c : ℝ}
    (hT : 0 < T) (hsmall : ε < 1 / 14) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    T ^ (1 / 2 - 3 * ε) * M * H * (c * M ^ (1 / 2 - ε)) +
      T ^ (1 / 2 - 7 * ε) * Hv *
        ((c * M ^ (1 + (1 / 2 - 3 * ε))) * (c * M ^ (1 / 2 - ε)) + c * M ^ (2 - 4 * ε)) +
      M ^ 2 * (c * M ^ (1 / 2 - ε)) * T ^ (-(1 / 2) - ε) +
      M * (c * M ^ (2 - 4 * ε)) * T ^ (-4 * ε) ≤
    2 * c * (T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
      T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
      T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
      T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)) := by
  let A := T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H
  let B := T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv
  let C := T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε)
  let D := T ^ (-4 * ε) * M ^ (3 - 4 * ε)
  let E := T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)
  have hm₁ : M * M ^ (1 / 2 - ε) = M ^ (3 / 2 - ε) := by
    calc
      _ = M ^ (1 : ℝ) * M ^ (1 / 2 - ε) := by rw [Real.rpow_one]
      _ = M ^ (1 + (1 / 2 - ε)) := (Real.rpow_add' hM (by linarith : 1 + (1 / 2 - ε) ≠ 0)).symm
      _ = _ := by congr 1; ring
  have hm₂ : M ^ (1 + (1 / 2 - 3 * ε)) * M ^ (1 / 2 - ε) = M ^ (2 - 4 * ε) := by
    rw [← Real.rpow_add' hM (by linarith : (1 + (1 / 2 - 3 * ε)) + (1 / 2 - ε) ≠ 0)]
    congr 1
    ring
  have hm₃ : M ^ (2 : ℕ) * M ^ (1 / 2 - ε) = M ^ (5 / 2 - ε) := by
    rw [← Real.rpow_two, ← Real.rpow_add' hM (by linarith : (2 : ℝ) + (1 / 2 - ε) ≠ 0)]
    congr 1
    ring
  have hm₄ : M * M ^ (2 - 4 * ε) = M ^ (3 - 4 * ε) := by
    calc
      _ = M ^ (1 : ℝ) * M ^ (2 - 4 * ε) := by rw [Real.rpow_one]
      _ = M ^ (1 + (2 - 4 * ε)) := (Real.rpow_add' hM (by linarith : 1 + (2 - 4 * ε) ≠ 0)).symm
      _ = _ := by congr 1; ring
  have hid : T ^ (1 / 2 - 3 * ε) * M * H * (c * M ^ (1 / 2 - ε)) +
      T ^ (1 / 2 - 7 * ε) * Hv *
        ((c * M ^ (1 + (1 / 2 - 3 * ε))) * (c * M ^ (1 / 2 - ε)) + c * M ^ (2 - 4 * ε)) +
      M ^ 2 * (c * M ^ (1 / 2 - ε)) * T ^ (-(1 / 2) - ε) +
      M * (c * M ^ (2 - 4 * ε)) * T ^ (-4 * ε) =
      c * A + (c ^ 2 + c) * B + c * C + c * D := by
    calc
      _ = c * T ^ (1 / 2 - 3 * ε) * H * (M * M ^ (1 / 2 - ε)) +
          T ^ (1 / 2 - 7 * ε) * Hv *
            (c ^ 2 * (M ^ (1 + (1 / 2 - 3 * ε)) * M ^ (1 / 2 - ε)) + c * M ^ (2 - 4 * ε)) +
          c * (M ^ 2 * M ^ (1 / 2 - ε)) * T ^ (-(1 / 2) - ε) +
          c * (M * M ^ (2 - 4 * ε)) * T ^ (-4 * ε) := by ring
      _ = _ := by rw [hm₁, hm₂, hm₃, hm₄]; dsimp only [A, B, C, D]; ring
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hcc : c ^ 2 + c ≤ 2 * c := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hcc hB
  have hca : 0 ≤ c * A := mul_nonneg hc hA
  have hcc' : 0 ≤ c * C := mul_nonneg hc hC
  have hcd : 0 ≤ c * D := mul_nonneg hc hD
  have hce : 0 ≤ c * E := mul_nonneg hc hE
  rw [hid]
  change c * A + (c ^ 2 + c) * B + c * C + c * D ≤ 2 * c * (A + B + C + D + E)
  nlinarith only [hm, hca, hcc', hcd, hce]

end GlobalPhi43.MW20
