module

public import GlobalPhi43.MW20.ParentScaleAlgebra

/-!
# Substitution of the parent coefficient row into the Holder rows
-/

public section

namespace GlobalPhi43.MW20

/-- A single uniform substitution yields the parent-amplitude bounds
corresponding to [MW20, (4.15)–(4.16)].
Its inputs are the coefficient and increment estimates, not a Schauder claim. -/
theorem parent_interpolation_substitution {d M c a b H N S : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hN : N ≤ 6 * (H * d ^ (a + b - 1) + d ^ (-1 : ℝ) * M +
      c * d ^ (a - 1) * M ^ (1 + a) + c * d ^ (b - 1) * M ^ (1 + b)))
    (hS : S ≤ d ^ b * H + 3 * c * M ^ (1 + a) +
      3 * c * d ^ (b - a) * M ^ (1 + b) + 3 * d ^ (1 - a) * N) :
    S ≤ 24 * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
      c * d ^ (b - a) * M ^ (1 + b)) := by
  have he (u w z : ℝ) (hz : u + w = z) : d ^ u * d ^ w = d ^ z := by
    rw [← Real.rpow_add hd, hz]
  have hw : 3 * d ^ (1 - a) * N ≤
      18 * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
        c * d ^ (b - a) * M ^ (1 + b)) := by
    calc
      _ ≤ 3 * d ^ (1 - a) *
          (6 * (H * d ^ (a + b - 1) + d ^ (-1 : ℝ) * M +
            c * d ^ (a - 1) * M ^ (1 + a) + c * d ^ (b - 1) * M ^ (1 + b))) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = 18 * ((d ^ (1 - a) * d ^ (a + b - 1)) * H +
          (d ^ (1 - a) * d ^ (-1 : ℝ)) * M +
          c * (d ^ (1 - a) * d ^ (a - 1)) * M ^ (1 + a) +
          c * (d ^ (1 - a) * d ^ (b - 1)) * M ^ (1 + b)) := by ring
      _ = _ := by
        rw [he (1 - a) (a + b - 1) b (by ring),
          he (1 - a) (-1) (-a) (by ring),
          he (1 - a) (a - 1) 0 (by ring),
          he (1 - a) (b - 1) (b - a) (by ring), Real.rpow_zero, mul_one]
  have h₁ : 0 ≤ d ^ b * H := by positivity
  have h₂ : 0 ≤ d ^ (-a) * M := by positivity
  have h₃ : 0 ≤ c * M ^ (1 + a) := by positivity
  have h₄ : 0 ≤ c * d ^ (b - a) * M ^ (1 + b) := by positivity
  nlinarith only [hS, hw, h₁, h₂, h₃, h₄]

end GlobalPhi43.MW20
