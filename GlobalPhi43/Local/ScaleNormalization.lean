/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry

/-! Exact powers under R=epsilon*L and T=epsilon²*L under scale normalization. -/
public section

namespace GlobalPhi43.Local

theorem scaled_rpow_product {ε L a b c : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (ε * L) ^ a * L ^ b * (ε ^ 2 * L) ^ c = ε ^ (a + 2 * c) * L ^ (a + b + c) := by
  have hs : (ε ^ 2) ^ c = ε ^ (2 * c) := by
    simpa only [Real.rpow_two] using (Real.rpow_mul hε.le (2 : ℝ) c).symm
  rw [Real.mul_rpow hε.le hL.le, Real.mul_rpow (sq_nonneg ε) hL.le, hs]
  calc
    _ = (ε ^ a * ε ^ (2 * c)) * ((L ^ a * L ^ b) * L ^ c) := by ring
    _ = _ := by rw [← Real.rpow_add hε, ← Real.rpow_add hL, ← Real.rpow_add hL]

theorem normalized_heat_factor {ε L γ : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (ε * L) ^ (-γ) * ((ε * L) / L) ^ 2 * L ^ γ = ε ^ (2 - γ) := by
  rw [mul_div_cancel_right₀ ε hL.ne']
  have hh := scaled_rpow_product (a := -γ) (b := γ) (c := 0) hε hL
  simp only [Real.rpow_zero, mul_one, mul_zero, add_zero, neg_add_cancel] at hh
  calc
    _ = ε ^ 2 * ((ε * L) ^ (-γ) * L ^ γ) := by ring
    _ = ε ^ 2 * ε ^ (-γ) := by rw [hh]
    _ = _ := by simpa only [Real.rpow_two, sub_eq_add_neg] using (Real.rpow_add hε (2 : ℝ) (-γ)).symm

theorem normalized_forcing_power {ε L γ β : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (ε * L) ^ (-γ) * L ^ (γ + 2 - β) * (ε ^ 2 * L) ^ (β - 2) = ε ^ (2 * β - 4 - γ) := by
  have hh := scaled_rpow_product (a := -γ) (b := γ + 2 - β) (c := β - 2) hε hL
  have he : -γ + 2 * (β - 2) = 2 * β - 4 - γ := by ring
  have hLexp : -γ + (γ + 2 - β) + (β - 2) = 0 := by ring
  simpa only [he, hLexp, Real.rpow_zero, mul_one] using hh

theorem normalized_near_smoothing_power {ε L γ β : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (ε * L) ^ (-γ) * (ε * L) ^ β * (ε ^ 2 * L) ^ (γ - β) = ε ^ (γ - β) := by
  rw [← Real.rpow_add (mul_pos hε hL)]
  have hh := scaled_rpow_product (a := -γ + β) (b := 0) (c := γ - β) hε hL
  have he : (-γ + β) + 2 * (γ - β) = γ - β := by ring
  have hLexp : (-γ + β) + 0 + (γ - β) = 0 := by ring
  simpa only [he, hLexp, Real.rpow_zero, mul_one] using hh

theorem normalized_far_smoothing_power {ε L γ β : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (ε * L) ^ (-γ) * ((ε * L) / L) ^ 2 * L ^ β * (ε ^ 2 * L) ^ (γ - β) =
      ε ^ (2 + γ - 2 * β) := by
  rw [mul_div_cancel_right₀ ε hL.ne']
  have hh := scaled_rpow_product (a := -γ) (b := β) (c := γ - β) hε hL
  have he : -γ + 2 * (γ - β) = γ - 2 * β := by ring
  have hLexp : -γ + β + (γ - β) = 0 := by ring
  rw [he, hLexp, Real.rpow_zero, mul_one] at hh
  calc
    _ = ε ^ 2 * ((ε * L) ^ (-γ) * L ^ β * (ε ^ 2 * L) ^ (γ - β)) := by ring
    _ = ε ^ 2 * ε ^ (γ - 2 * β) := by rw [hh]
    _ = ε ^ (2 + (γ - 2 * β)) := by
      simpa only [Real.rpow_two] using (Real.rpow_add hε (2 : ℝ) (γ - 2 * β)).symm
    _ = _ := by congr 1; ring

end GlobalPhi43.Local
