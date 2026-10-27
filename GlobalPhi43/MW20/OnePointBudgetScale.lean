module

public import GlobalPhi43.MW20.OnePointMajorant

/-!
# The heat forcing pays the actual one-point Schauder scale budget
-/

public section

namespace GlobalPhi43.MW20

/-- Nonnegativity of the explicit source coefficient, independent of T. -/
theorem sourceOnePointMajorant_nonneg {ε L M H Hv HU Hν N c : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv)
    (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν) (hN : 0 ≤ N) (hc : 0 ≤ c) :
    0 ≤ sourceOnePointMajorant ε L M H Hv HU Hν N c := by
  unfold sourceOnePointMajorant sourceFirstProductScale sourceSecondProductScale
  positivity

/-- Exact two-exponent scale extraction from the complete quantitative
forcing budget. The two powers are γ and β, with their actual L^(γ−β). -/
theorem source_small_scale_budget_heat_scale {ε T L M H Hv HU Hν N c : ℝ}
    (hT : 0 < T) (hTL : T ≤ L) (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU)
    (hHν : 0 ≤ Hν) (hN : 0 ≤ N) (hc : 0 ≤ c) :
    T ^ 2 * (M ^ 3 + L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c * Hv * M ^ (1 - 2 * ε) +
      c * sourceFirstProductBudget ε T M H Hv + c * sourceSecondProductBudget ε T M Hv HU Hν N) ≤
    sourceOnePointMajorant ε L M H Hv HU Hν N c *
      (T ^ (3 / 2 - 5 * ε) + T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε)) := by
  have hL : 0 ≤ L := hT.le.trans hTL
  obtain ⟨h₀, _, _, _, _, _, _⟩ := mw20_heat_test_powers hT hTL hε hsmall
  have hm := mul_le_mul_of_nonneg_right h₀ (pow_nonneg hM 3)
  have hf := mul_le_mul_of_nonneg_left
    (sourceFirstProductBudget_heat_scale hT hTL hε hsmall hM hH hHv) hc
  have hg := mul_le_mul_of_nonneg_left
    (sourceSecondProductBudget_heat_scale hT hTL hε hsmall hM hHv hHU hHν hN) hc
  have he : T ^ 2 * (L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c * Hv * M ^ (1 - 2 * ε)) =
      (c * Hv * M ^ (1 - 2 * ε)) * (T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε)) := by
    have hp : T ^ (2 : ℕ) * T ^ (-1 - 2 * ε) = T ^ (1 - 2 * ε) := by
      rw [← Real.rpow_two, ← Real.rpow_add hT]
      congr 1
      ring
    calc
      _ = (T ^ 2 * T ^ (-1 - 2 * ε)) * L ^ (1 / 2 - 3 * ε) * c * Hv * M ^ (1 - 2 * ε) := by ring
      _ = _ := by rw [hp]; ring
  let A := L ^ (1 / 2 + 5 * ε) * M ^ 3 +
    c * sourceFirstProductScale ε L M H Hv + c * sourceSecondProductScale ε L M Hv HU Hν N
  let B := c * Hv * M ^ (1 - 2 * ε)
  let P := T ^ (3 / 2 - 5 * ε)
  let Q := T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε)
  have hA : 0 ≤ A := by dsimp only [A, sourceFirstProductScale, sourceSecondProductScale]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  calc
    _ ≤ A * P + B * Q := by dsimp only [A, B, P, Q]; nlinarith only [hm, hf, hg, he]
    _ ≤ (A + B) * (P + Q) := by nlinarith only [mul_nonneg hA hQ, mul_nonneg hB hP]
    _ = _ := by dsimp only [A, B, P, Q, sourceOnePointMajorant]; ring

/-- The coefficient is monotone in the permitted testing radius. -/
theorem sourceOnePointMajorant_mono {ε L K M H Hv HU Hν N c : ℝ}
    (hL : 0 ≤ L) (hLK : L ≤ K) (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU)
    (hHν : 0 ≤ Hν) (hN : 0 ≤ N) (hc : 0 ≤ c) :
    sourceOnePointMajorant ε L M H Hv HU Hν N c ≤ sourceOnePointMajorant ε K M H Hv HU Hν N c := by
  unfold sourceOnePointMajorant sourceFirstProductScale sourceSecondProductScale
  gcongr <;> linarith

end GlobalPhi43.MW20
