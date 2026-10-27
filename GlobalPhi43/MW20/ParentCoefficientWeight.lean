module

public import GlobalPhi43.MW20.ParentCoefficientAlgebra

/-!
# Reciprocal-scale weight of the parent-amplitude bound corresponding to [MW20, (4.17)]
-/

public section

namespace GlobalPhi43.MW20

/-- Every term in the parent coefficient envelope has the required weighted
size on dM≤1. Both squared smallness terms retain their actual coefficient. -/
theorem parent_coefficient_envelope_weight {d M c a b H : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H) (hscale : d * M ≤ 1) :
    d ^ (a + b) * ((1 + c * d ^ b * M ^ b) * H + c ^ 2 * M ^ (1 + (a + b)) +
      c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b) + d ^ (-(a + b)) * M +
      c * d ^ (-b) * M ^ (1 + a) + c * d ^ (-a) * M ^ (1 + b)) ≤
      5 * (d ^ (a + b) * H + M) := by
  have hc₂ : c ^ 2 ≤ 1 := by nlinarith
  have hγ := parent_tree_weight hd hM (sq_nonneg c) hc₂ (show 0 ≤ a + b by linarith) hscale
  have h₂b := parent_tree_weight hd hM (sq_nonneg c) hc₂ (show 0 ≤ 2 * b by linarith) hscale
  have hₐ := parent_tree_weight hd hM hc hc1 ha hscale
  have hᵦ := parent_tree_weight hd hM hc hc1 hb hscale
  have hm : M ^ (1 + b) = M * M ^ b := by rw [Real.rpow_add hM, Real.rpow_one]
  have hq : c * d ^ b * M ^ b ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ hM
    calc
      (c * d ^ b * M ^ b) * M = c * d ^ b * M ^ (1 + b) := by rw [hm]; ring
      _ ≤ M := hᵦ
      _ = 1 * M := by ring
  have hW : 0 ≤ d ^ (a + b) * H := by positivity
  have hqW := mul_le_mul_of_nonneg_right hq hW
  have he (u v w : ℝ) (hw : u + v = w) : d ^ u * d ^ v = d ^ w := by
    rw [← Real.rpow_add hd, hw]
  have hid : d ^ (a + b) * ((1 + c * d ^ b * M ^ b) * H + c ^ 2 * M ^ (1 + (a + b)) +
      c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b) + d ^ (-(a + b)) * M +
      c * d ^ (-b) * M ^ (1 + a) + c * d ^ (-a) * M ^ (1 + b)) =
      d ^ (a + b) * H + (c * d ^ b * M ^ b) * (d ^ (a + b) * H) +
        c ^ 2 * d ^ (a + b) * M ^ (1 + (a + b)) +
        c ^ 2 * d ^ (2 * b) * M ^ (1 + 2 * b) + M +
        c * d ^ a * M ^ (1 + a) + c * d ^ b * M ^ (1 + b) := by
    calc
      _ = d ^ (a + b) * H + (c * d ^ b * M ^ b) * (d ^ (a + b) * H) +
          c ^ 2 * d ^ (a + b) * M ^ (1 + (a + b)) +
          c ^ 2 * (d ^ (a + b) * d ^ (b - a)) * M ^ (1 + 2 * b) +
          (d ^ (a + b) * d ^ (-(a + b))) * M +
          c * (d ^ (a + b) * d ^ (-b)) * M ^ (1 + a) +
          c * (d ^ (a + b) * d ^ (-a)) * M ^ (1 + b) := by ring
      _ = _ := by
        rw [he (a + b) (b - a) (2 * b) (by ring),
          he (a + b) (-(a + b)) 0 (by ring), he (a + b) (-b) a (by ring),
          he (a + b) (-a) b (by ring), Real.rpow_zero, one_mul]
  rw [hid]
  nlinarith only [hqW, hγ, h₂b, hₐ, hᵦ, hW]

end GlobalPhi43.MW20
