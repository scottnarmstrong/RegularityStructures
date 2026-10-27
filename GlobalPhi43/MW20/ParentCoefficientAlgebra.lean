module

public import GlobalPhi43.MW20.ParentInterpolationAlgebra

/-!
# The parent-amplitude substitution corresponding to [MW20, (4.17)]
-/

public section

namespace GlobalPhi43.MW20

/-- Substitute the parent-amplitude form of [MW20, (4.16)] and the bound
[MW20, (4.13)] into the coefficient Hölder estimate.
Every amplitude is the same parent M. The constant depends only on a+b. -/
theorem parent_coefficient_holder_substitution {d M c a b H V : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hV : V ≤ 24 * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
      c * d ^ (b - a) * M ^ (1 + b))) :
    H + 3 * V * (c * M ^ b) + (d / 2) ^ (-(a + b)) *
      (2 * M + c * d ^ a * M ^ (1 + a) + 3 * c * d ^ b * M ^ (1 + b)) ≤
    100 * (1 + 2 ^ (a + b)) *
      ((1 + c * d ^ b * M ^ b) * H + c ^ 2 * M ^ (1 + (a + b)) +
        c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b) + d ^ (-(a + b)) * M +
        c * d ^ (-b) * M ^ (1 + a) + c * d ^ (-a) * M ^ (1 + b)) := by
  let B := c * d ^ b * M ^ b * H
  let C := c ^ 2 * M ^ (1 + (a + b))
  let D := c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b)
  let E := d ^ (-(a + b)) * M
  let F := c * d ^ (-b) * M ^ (1 + a)
  let G := c * d ^ (-a) * M ^ (1 + b)
  let η := (2 : ℝ) ^ (a + b)
  let S := H + B + C + D + E + F + G
  have hm₀ : M * M ^ b = M ^ (1 + b) := by
    nth_rw 1 [← Real.rpow_one M]
    rw [← Real.rpow_add hM]
  have hm₁ : M ^ (1 + a) * M ^ b = M ^ (1 + (a + b)) := by
    rw [← Real.rpow_add hM]; congr 1; ring
  have hm₂ : M ^ (1 + b) * M ^ b = M ^ (1 + 2 * b) := by
    rw [← Real.rpow_add hM]; congr 1; ring
  have hv : 3 * V * (c * M ^ b) ≤ 72 * (B + G + C + D) := by
    calc
      _ ≤ 3 * (24 * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
          c * d ^ (b - a) * M ^ (1 + b))) * (c * M ^ b) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) (by positivity)
      _ = 72 * (c * d ^ b * M ^ b * H + c * d ^ (-a) * (M * M ^ b) +
          c ^ 2 * (M ^ (1 + a) * M ^ b) +
          c ^ 2 * d ^ (b - a) * (M ^ (1 + b) * M ^ b)) := by ring
      _ = _ := by rw [hm₀, hm₁, hm₂]
  have hhalf : (d / 2) ^ (-(a + b)) = η * d ^ (-(a + b)) := by
    rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp only [η]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hd₁ : d ^ (-(a + b)) * d ^ a = d ^ (-b) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have hd₂ : d ^ (-(a + b)) * d ^ b = d ^ (-a) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have hu : (d / 2) ^ (-(a + b)) *
      (2 * M + c * d ^ a * M ^ (1 + a) + 3 * c * d ^ b * M ^ (1 + b)) =
      η * (2 * E + F + 3 * G) := by
    rw [hhalf]
    calc
      _ = η * (2 * (d ^ (-(a + b)) * M) +
          c * (d ^ (-(a + b)) * d ^ a) * M ^ (1 + a) +
          3 * c * (d ^ (-(a + b)) * d ^ b) * M ^ (1 + b)) := by ring
      _ = _ := by rw [hd₁, hd₂]; dsimp only [E, F, G]; ring
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hnear : H + 72 * (B + G + C + D) ≤ 72 * S := by
    dsimp only [S]; linarith
  have hfar : η * (2 * E + F + 3 * G) ≤ 3 * η * S := by
    have ht : 2 * E + F + 3 * G ≤ 3 * S := by dsimp only [S]; linarith
    nlinarith only [mul_le_mul_of_nonneg_left ht hη]
  have hηS : 0 ≤ η * S := mul_nonneg hη hS
  have hsum : (1 + c * d ^ b * M ^ b) * H + c ^ 2 * M ^ (1 + (a + b)) +
      c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b) + d ^ (-(a + b)) * M +
      c * d ^ (-b) * M ^ (1 + a) + c * d ^ (-a) * M ^ (1 + b) = S := by
    dsimp only [S, B, C, D, E, F, G]; ring
  rw [hu, hsum]
  change H + 3 * V * (c * M ^ b) + η * (2 * E + F + 3 * G) ≤ 100 * (1 + η) * S
  nlinarith only [hv, hnear, hfar, hS, hηS]

end GlobalPhi43.MW20
