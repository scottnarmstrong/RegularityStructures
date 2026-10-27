module

public import GlobalPhi43.MW20.Telescoping

/-! The Lemma 2.10 reconstruction and local tests in the printed additive
budget, with a constant depending only on the source loss exponent. -/

public section

namespace GlobalPhi43.MW20

/-- Data-independent comparison constant for MW20 (2.33). -/
@[expose] noncomputable def secondProductConstant (ε : ℝ) : ℝ :=
  3 / (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) + 3

theorem secondProductConstant_pos {ε : ℝ} (hsmall : ε < 1 / 14) : 0 < secondProductConstant ε := by
  have hγ : 0 < (1 / 2 : ℝ) - 7 * ε := by linarith
  have hd : 0 < 1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε) := sub_pos.2
    (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  unfold secondProductConstant
  positivity

/-- No counterterm-size estimate or product of source budgets is introduced. -/
theorem secondProduct_budget_le {T ε Hv HU Hν NA NV NX M N ND : ℝ}
    (hT : 0 < T) (hsmall : ε < 1 / 14)
    (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν) (hNA : 0 ≤ NA) (hNV : 0 ≤ NV) (hNX : 0 ≤ NX)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hND : 0 ≤ ND) :
    (3 * Hv * NA + HU * NV + 3 * Hν * NX) * T ^ (1 / 2 - 7 * ε) /
        (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) +
      ND * T ^ (-(1 / 2) - 5 * ε) + 3 * M * (NA * T ^ (-4 * ε)) + 3 * N * (NX * T ^ (-2 * ε)) ≤
    secondProductConstant ε *
      (T ^ (1 / 2 - 7 * ε) * (Hv * NA + HU * NV + Hν * NX) +
        ND * T ^ (-(1 / 2) - 5 * ε) + T ^ (-4 * ε) * M * NA + N * NX * T ^ (-2 * ε)) := by
  let d : ℝ := 1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)
  let a : ℝ := T ^ (1 / 2 - 7 * ε) * (Hv * NA + HU * NV + Hν * NX)
  let b : ℝ := ND * T ^ (-(1 / 2) - 5 * ε)
  let c : ℝ := T ^ (-4 * ε) * M * NA
  let e : ℝ := N * NX * T ^ (-2 * ε)
  have hγ : 0 < (1 / 2 : ℝ) - 7 * ε := by linarith
  have hd : 0 < d := sub_pos.2 (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hnum : (3 * Hv * NA + HU * NV + 3 * Hν * NX) * T ^ (1 / 2 - 7 * ε) ≤ 3 * a := by
    have hh : 0 ≤ HU * NV * T ^ (1 / 2 - 7 * ε) := by positivity
    dsimp [a]
    nlinarith only [hh]
  have hKrec : 3 / d ≤ secondProductConstant ε := by change 3 / d ≤ 3 / d + 3; linarith
  have hK : 3 ≤ secondProductConstant ε := by
    change 3 ≤ 3 / d + 3
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hd.le]
  have hKa := mul_le_mul_of_nonneg_right hKrec ha
  have hKb := mul_le_mul_of_nonneg_right (show 1 ≤ secondProductConstant ε by linarith) hb
  have hKc := mul_le_mul_of_nonneg_right hK hc
  have hKe := mul_le_mul_of_nonneg_right hK he
  have hbound : 3 * a / d + b + 3 * c + 3 * e ≤ secondProductConstant ε * (a + b + c + e) := by
    have hid : 3 * a / d = (3 / d) * a := by ring
    rw [hid]
    nlinarith only [hKa, hKb, hKc, hKe]
  apply le_trans _ hbound
  have hh := div_le_div_of_nonneg_right hnum hd.le
  dsimp [d, b, c, e] at hh ⊢
  nlinarith only [hh]

end GlobalPhi43.MW20
