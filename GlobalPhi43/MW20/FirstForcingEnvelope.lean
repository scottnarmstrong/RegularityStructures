module

public import GlobalPhi43.MW20.ForcingMonomialMajorants

/-! The actual first forcing envelope has cubic parent amplitude. -/

public section

namespace GlobalPhi43.MW20

/-- All five actual first-product terms have one common scale majorant. -/
theorem first_forcing_envelope_bound {M k C ε : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hC : 0 ≤ C)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) :
    let T := (1 / M) / k
    let d := (1 / M) * (k - 1) / k
    T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * (C * M / d ^ (1 - 2 * ε)) +
      T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * (C * M / d ^ (1 / 2 - 3 * ε)) +
      T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) +
      T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
      T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε) ≤
      (C * (2 : ℝ) ^ (1 - 2 * ε) + C * (2 : ℝ) ^ (1 / 2 - 3 * ε) + 3) *
        (M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε)) := by
  have h₁ := parent_forcing_monomial_majorant (a := 1 / 2 - 3 * ε)
    (b := 3 / 2 - ε) (s := 1 - 2 * ε) (q := 3 / 2 + 3 * ε)
    hM hk hC (by linarith) (by ring) (by linarith)
  have h₂ := parent_forcing_monomial_majorant (a := 1 / 2 - 7 * ε)
    (b := 2 - 4 * ε) (s := 1 / 2 - 3 * ε) (q := 3 / 2 + 3 * ε)
    hM hk hC (by linarith) (by ring) (by linarith)
  have h₃ := plain_forcing_monomial_majorant (a := -(1 / 2) - ε)
    (b := 5 / 2 - ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  have h₄ := plain_forcing_monomial_majorant (a := -4 * ε)
    (b := 3 - 4 * ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  have h₅ := plain_forcing_monomial_majorant (a := 1 / 2 - 7 * ε)
    (b := 7 / 2 - 7 * ε) (q := 3 / 2 + 3 * ε) hM hk (by ring) (by linarith)
  dsimp only
  nlinarith only [h₁, h₂, h₃, h₄, h₅]

end GlobalPhi43.MW20
