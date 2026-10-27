module

public import GlobalPhi43.MW20.ForcingMonomialMajorants

/-! Cubic parent majorant for all second-product terms. -/

public section

namespace GlobalPhi43.MW20

/-- The actual second-product envelope, with the coefficient and full
expansion contributions kept separately until after their estimates. -/
theorem second_forcing_envelope_bound {M k Cv CU Cν CN ε : ℝ}
    (hM : 0 < M) (hk : 2 < k)
    (hCv : 0 ≤ Cv) (hCU : 0 ≤ CU) (hCν : 0 ≤ Cν) (hCN : 0 ≤ CN)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) :
    let T := (1 / M) / k
    let d := (1 / M) * (k - 1) / k
    let γ := (3 / 2 : ℝ) - 5 * ε
    T ^ (1 / 2 - 7 * ε) *
        ((Cv * M / d ^ (1 / 2 - 3 * ε)) * M ^ (2 - 4 * ε) +
          ((CU * M / d ^ γ) + (Cν * M / d ^ γ)) * M ^ (1 - 2 * ε)) +
      M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
      T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
      (CN * M / d) * M ^ (1 - 2 * ε) * T ^ (-2 * ε) ≤
      (Cv * (2 : ℝ) ^ (1 / 2 - 3 * ε) + CU * (2 : ℝ) ^ γ +
        Cν * (2 : ℝ) ^ γ + 2 + 2 * CN) *
        (M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε)) := by
  have h₁ := parent_forcing_monomial_majorant (a := 1 / 2 - 7 * ε)
    (b := 2 - 4 * ε) (s := 1 / 2 - 3 * ε) (q := 3 / 2 + 3 * ε)
    hM hk hCv (by linarith) (by ring) (by linarith)
  have h₂ := parent_forcing_monomial_majorant (a := 1 / 2 - 7 * ε)
    (b := 1 - 2 * ε) (s := 3 / 2 - 5 * ε) (q := 3 / 2 + 3 * ε)
    hM hk hCU (by linarith) (by ring) (by linarith)
  have h₃ := parent_forcing_monomial_majorant (a := 1 / 2 - 7 * ε)
    (b := 1 - 2 * ε) (s := 3 / 2 - 5 * ε) (q := 3 / 2 + 3 * ε)
    hM hk hCν (by linarith) (by ring) (by linarith)
  have h₄ := plain_forcing_monomial_majorant (a := -(1 / 2) - 5 * ε)
    (b := 5 / 2 - 5 * ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  have h₅ := plain_forcing_monomial_majorant (a := -4 * ε)
    (b := 3 - 4 * ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  have h₆ := parent_forcing_monomial_majorant (a := -2 * ε)
    (b := 1 - 2 * ε) (s := 1) (q := 3 / 2 + 3 * ε)
    hM hk hCN (by norm_num) (by ring) (by linarith)
  rw [Real.rpow_one, Real.rpow_one] at h₆
  dsimp only
  nlinarith only [h₁, h₂, h₃, h₄, h₅, h₆]

/-- The ordinary V contribution to complete B also has cubic degree. -/
theorem ordinary_V_forcing_envelope_bound {M k ε : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hε : 0 < ε) :
    M * (M ^ (1 - 2 * ε) * (((1 / M) / k) ^ (-1 - 2 * ε))) ≤
      M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) := by
  have he : 2 - 2 * ε = 1 + (1 - 2 * ε) := by ring
  have h := plain_forcing_monomial_majorant (a := -1 - 2 * ε)
    (b := 2 - 2 * ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  rw [he, Real.rpow_add hM, Real.rpow_one] at h
  convert h using 1; ring

end GlobalPhi43.MW20
