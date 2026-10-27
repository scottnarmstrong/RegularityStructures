/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CoefficientProbe

/-! Large-distance remainder estimates for the radius-local Schauder estimate. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped BigOperators

/-- The spatial linear form uses the sup norm on the three source coordinates. -/
theorem spatialLinear_abs_le (ν : Fin 3 → ℝ) (x y : ParabolicSpace) {N : ℝ}
    (hN : 0 ≤ N) (hν : ∀ i, |ν i| ≤ N) :
    |spatialLinear ν (y - x)| ≤ 3 * N * pdist x y := by
  calc
    _ ≤ ∑ i : Fin 3, |ν i * (y.2 i - x.2 i)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, N * pdist x y := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul (hν i) _ (abs_nonneg _) hN
      have hi := norm_le_pi_norm (y.2 - x.2) i
      have hp : ‖y.2 - x.2‖ ≤ pdist x y := by
        rw [norm_sub_rev]; exact le_max_right _ _
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi.trans hp
    _ = _ := by simp; ring

/-- Division by the actual pair distance gives the two exact scalar powers. -/
theorem large_ratio_bound {a q γ B N : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (hγ : 1 ≤ γ) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    (B + N * q) / q ^ γ ≤ B / a ^ γ + N / a ^ (γ - 1) := by
  have hq : 0 < q := ha.trans_le haq
  have hpow : q ^ γ = q ^ (γ - 1) * q := by
    calc
      q ^ γ = q ^ ((γ - 1) + 1) := by congr 1; ring
      _ = q ^ (γ - 1) * q ^ (1 : ℝ) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  have heq : N * q / q ^ γ = N / q ^ (γ - 1) := by
    rw [hpow]
    field_simp
  rw [add_div, heq]
  apply add_le_add
  · exact div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos ha _)
      (Real.rpow_le_rpow ha.le haq (by linarith))
  · exact div_le_div_of_nonneg_left hN (Real.rpow_pos_of_pos ha _)
      (Real.rpow_le_rpow ha.le haq (by linarith))

/-- A d-weighted coefficient bound and the original U budget control all
pairs at distance at least a*d, irrespective of their time order. -/
theorem large_remainder_bound
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x y : ParabolicSpace) {d a γ B N : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hγ : 1 ≤ γ) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hfar : a * d ≤ pdist x y) (hU : |U x y| ≤ B)
    (hν : ∀ i, d * |ν x i| ≤ N) :
    |affineRemainder U ν x y| / (pdist x y / d) ^ γ ≤
      B / a ^ γ + 3 * N / a ^ (γ - 1) := by
  have hcoeff : ∀ i, |ν x i| ≤ N / d := fun i =>
    (le_div_iff₀ hd).2 (by simpa only [mul_comm] using hν i)
  have hlin := spatialLinear_abs_le (ν x) x y (div_nonneg hN hd.le) hcoeff
  have hrem : |affineRemainder U ν x y| ≤ B + 3 * N * (pdist x y / d) := by
    calc
      _ ≤ |U x y| + |spatialLinear (ν x) (y - x)| := abs_sub _ _
      _ ≤ B + 3 * (N / d) * pdist x y := add_le_add hU hlin
      _ = _ := by ring
  have haq : a ≤ pdist x y / d := (le_div_iff₀ hd).2 hfar
  exact (div_le_div_of_nonneg_right hrem (Real.rpow_nonneg (div_nonneg (pdist_nonneg x y) hd.le) _)).trans
    (large_ratio_bound ha haq hγ hB (by positivity))

end GlobalPhi43.Local
