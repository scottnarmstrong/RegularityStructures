module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Parent-amplitude interpolation at the reciprocal-amplitude scale

Numerical consequences of parent-amplitude coefficient and Schauder
bounds associated with [MW20, (4.14)–(4.16)]. The analytic bounds are hypotheses.
-/

public section

namespace GlobalPhi43.MW20

/-- The parent tree term costs only M at the actual scale dM≤1. -/
theorem parent_tree_weight {d M c a : ℝ} (hd : 0 < d) (hM : 0 < M)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ha : 0 ≤ a) (hscale : d * M ≤ 1) :
    c * d ^ a * M ^ (1 + a) ≤ M := by
  have hp := Real.rpow_le_one (mul_nonneg hd.le hM.le) hscale ha
  rw [Real.mul_rpow hd.le hM.le] at hp
  have hcp : c * (d ^ a * M ^ a) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp hc).trans (by simpa using hc1)
  have h := mul_le_mul_of_nonneg_right hcp hM.le
  have he : M ^ (1 + a) = M ^ a * M := by
    rw [Real.rpow_add hM, Real.rpow_one]
    ring
  rw [he]
  nlinarith only [h]


/-- Weighted parent-amplitude bound corresponding to [MW20, (4.14)]. The constant is uniform in d,M,c and the data. -/
theorem parent_coefficient_weight {d M c α β H N C : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hscale : d * M ≤ 1)
    (hN : N ≤ C * (d ^ (α + β - 1) * H + d ^ (-1 : ℝ) * M +
      c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β))) :
    d * N ≤ 3 * C * (d ^ (α + β) * H + M) := by
  have hαw := parent_tree_weight hd hM hc hc1 hα hscale
  have hβw := parent_tree_weight hd hM hc hc1 hβ hscale
  have hw := mul_le_mul_of_nonneg_left hN hd.le
  have he (a : ℝ) : d * d ^ (a - 1) = d ^ a := by
    nth_rw 1 [← Real.rpow_one d]
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hzero : d * d ^ (-1 : ℝ) = 1 := by
    simpa only [zero_sub, Real.rpow_zero] using he 0
  have hid : d * (C * (d ^ (α + β - 1) * H + d ^ (-1 : ℝ) * M +
      c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β))) =
      C * (d ^ (α + β) * H + M + c * d ^ α * M ^ (1 + α) +
        c * d ^ β * M ^ (1 + β)) := by
    calc
      _ = C * ((d * d ^ (α + β - 1)) * H + (d * d ^ (-1 : ℝ)) * M +
          c * (d * d ^ (α - 1)) * M ^ (1 + α) +
          c * (d * d ^ (β - 1)) * M ^ (1 + β)) := by ring
      _ = _ := by rw [he, hzero, he, he, one_mul]
  rw [hid] at hw
  have ht : C * (d ^ (α + β) * H + M + c * d ^ α * M ^ (1 + α) +
      c * d ^ β * M ^ (1 + β)) ≤ C * (d ^ (α + β) * H + 3 * M) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hp : 0 ≤ C * (d ^ (α + β) * H) := by positivity
  nlinarith only [hw, ht, hp]

/-- Weighted parent-amplitude bounds corresponding to [MW20, (4.15)–(4.16)], with the two Holder exponents interchanged.
Both tree contributions retain the parent amplitude throughout. -/
theorem parent_holder_weight {d M c a b H V C : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hscale : d * M ≤ 1)
    (hV : V ≤ C * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
      c * d ^ (b - a) * M ^ (1 + b))) :
    d ^ a * V ≤ 3 * C * (d ^ (a + b) * H + M) := by
  have haw := parent_tree_weight hd hM hc hc1 ha hscale
  have hbw := parent_tree_weight hd hM hc hc1 hb hscale
  have hw := mul_le_mul_of_nonneg_left hV (Real.rpow_nonneg hd.le a)
  have he₁ : d ^ a * d ^ b = d ^ (a + b) := (Real.rpow_add hd a b).symm
  have he₂ : d ^ a * d ^ (-a) = 1 := by
    rw [← Real.rpow_add hd, add_neg_cancel, Real.rpow_zero]
  have he₃ : d ^ a * d ^ (b - a) = d ^ b := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hid : d ^ a * (C * (d ^ b * H + d ^ (-a) * M + c * M ^ (1 + a) +
      c * d ^ (b - a) * M ^ (1 + b))) =
      C * (d ^ (a + b) * H + M + c * d ^ a * M ^ (1 + a) +
        c * d ^ b * M ^ (1 + b)) := by
    calc
      _ = C * ((d ^ a * d ^ b) * H + (d ^ a * d ^ (-a)) * M +
          c * d ^ a * M ^ (1 + a) + c * (d ^ a * d ^ (b - a)) * M ^ (1 + b)) := by ring
      _ = _ := by rw [he₁, he₂, he₃, one_mul]
  rw [hid] at hw
  have ht : C * (d ^ (a + b) * H + M + c * d ^ a * M ^ (1 + a) +
      c * d ^ b * M ^ (1 + b)) ≤ C * (d ^ (a + b) * H + 3 * M) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hp : 0 ≤ C * (d ^ (a + b) * H) := by positivity
  nlinarith only [hw, ht, hp]

end GlobalPhi43.MW20
