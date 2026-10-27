module

public import GlobalPhi43.MW20.Telescoping

/-! Put the first-product budget into the exact four printed source
budgets. The chosen comparison constant depends only on the loss exponent. -/

public section

namespace GlobalPhi43.MW20

/-- An explicit data-independent comparison constant for MW20 (2.32). -/
@[expose] noncomputable def firstProductConstant (ε : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (4 * ε) + 2) / (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) + 2

theorem firstProductConstant_pos {ε : ℝ} (hsmall : ε < 1 / 14) : 0 < firstProductConstant ε := by
  have hγ : 0 < (1 / 2 : ℝ) - 7 * ε := by linarith
  have hd : 0 < 1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε) := sub_pos.2
    (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  unfold firstProductConstant
  positivity

/-- The explicit telescope and local-test bounds imply the four
printed Lemma 2.9 budgets, with no data or individual-rate dependence in K. -/
theorem firstProduct_budget_le {T ε M H Hv HZ NJ NB : ℝ}
    (hT : 0 < T) (hsmall : ε < 1 / 14)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ) (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) :
    ((2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ) * T ^ (1 / 2 - 7 * ε) +
      (2 * Hv * NB) * T ^ (1 / 2 - 7 * ε)) / (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) +
      M ^ 2 * (NJ * T ^ (-(1 / 2) - ε)) + 2 * M * (NB * T ^ (-4 * ε)) ≤
    firstProductConstant ε *
      (T ^ (1 / 2 - 3 * ε) * M * H * NJ +
        T ^ (1 / 2 - 7 * ε) * Hv * (HZ * NJ + NB) +
        M ^ 2 * NJ * T ^ (-(1 / 2) - ε) + M * NB * T ^ (-4 * ε)) := by
  let γ : ℝ := 1 / 2 - 7 * ε
  let d : ℝ := 1 - (1 / 2 : ℝ) ^ γ
  let p : ℝ := 2 * (2 : ℝ) ^ (4 * ε)
  let a : ℝ := T ^ (1 / 2 - 3 * ε) * M * H * NJ
  let b : ℝ := T ^ γ * Hv * (HZ * NJ + NB)
  let c : ℝ := M ^ 2 * NJ * T ^ (-(1 / 2) - ε)
  let e : ℝ := M * NB * T ^ (-4 * ε)
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hd : 0 < d := sub_pos.2 (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hpower : (2 * T) ^ (4 * ε) * T ^ γ = (2 : ℝ) ^ (4 * ε) * T ^ (1 / 2 - 3 * ε) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT.le, mul_assoc, ← Real.rpow_add hT]
    congr 2
    dsimp [γ]
    ring
  have hnum : (2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ) * T ^ γ +
      (2 * Hv * NB) * T ^ γ = p * a + T ^ γ * Hv * (HZ * NJ + 2 * NB) := by
    calc
      _ = 2 * M * H * NJ * ((2 * T) ^ (4 * ε) * T ^ γ) + T ^ γ * Hv * (HZ * NJ + 2 * NB) := by ring
      _ = _ := by rw [hpower]; dsimp [p, a]; ring
  have hnumle : (2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ) * T ^ γ +
      (2 * Hv * NB) * T ^ γ ≤ p * a + 2 * b := by
    rw [hnum]
    have hn : 0 ≤ T ^ γ * Hv * HZ * NJ := by positivity
    dsimp [b]
    nlinarith only [hn]
  have hKp : p / d ≤ firstProductConstant ε := by
    change p / d ≤ (p + 2) / d + 2
    linarith [div_le_div_of_nonneg_right (show p ≤ p + 2 by linarith) hd.le]
  have hKtwo : 2 / d ≤ firstProductConstant ε := by
    change 2 / d ≤ (p + 2) / d + 2
    linarith [div_le_div_of_nonneg_right (show 2 ≤ p + 2 by linarith) hd.le]
  have hK : 2 ≤ firstProductConstant ε := by
    change 2 ≤ (p + 2) / d + 2
    have hh : 0 ≤ (p + 2) / d := div_nonneg (by linarith) hd.le
    linarith
  have hKa := mul_le_mul_of_nonneg_right hKp ha
  have hKb := mul_le_mul_of_nonneg_right hKtwo hb
  have hKc := mul_le_mul_of_nonneg_right (show 1 ≤ firstProductConstant ε by linarith) hc
  have hKe := mul_le_mul_of_nonneg_right hK he
  have hbudget : (p * a + 2 * b) / d + c + 2 * e ≤ firstProductConstant ε * (a + b + c + e) := by
    have hid : (p * a + 2 * b) / d = (p / d) * a + (2 / d) * b := by ring
    rw [hid]
    nlinarith only [hKa, hKb, hKc, hKe]
  apply le_trans _ hbudget
  change _ ≤ (p * a + 2 * b) / d + c + 2 * e
  have hh := div_le_div_of_nonneg_right hnumle hd.le
  dsimp [d, γ, c, e] at hh ⊢
  nlinarith only [hh]

end GlobalPhi43.MW20
