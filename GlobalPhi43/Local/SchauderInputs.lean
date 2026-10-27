/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.Algebra
public import GlobalPhi43.Local.RadiusGeometry

/-! Pointwise inputs to the corrected radius-local Schauder proof, part1:760–785.
The seminorm/PDE estimates supplying the displayed pointwise bounds are still
analytic obligations; these lemmas do not add them to the source contract. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures

/-- Exact three-point input from the two Hölder increments, including the
factor 3 and the different exponents of v and Y. -/
theorem expansion_three_point_bound {κ V H : ℝ}
    (v Y Z : ParabolicSpace → ℝ) (x y z : ParabolicSpace)
    (hV : 0 ≤ V)
    (hv : |v y - v x| ≤ V * pdist x y ^ (1 / 2 - 3 * κ))
    (hY : |Y z - Y y| ≤ H * pdist y z ^ (1 - 2 * κ)) :
    |expansion v Y Z x z - expansion v Y Z x y - expansion v Y Z y z| ≤
      3 * V * H * pdist x y ^ (1 / 2 - 3 * κ) *
        pdist y z ^ ((3 / 2 - 5 * κ) - (1 / 2 - 3 * κ)) := by
  have hprod := mul_le_mul hv hY (abs_nonneg (Y z - Y y))
    (mul_nonneg hV (Real.rpow_nonneg (pdist_nonneg x y) _))
  calc
    _ = 3 * (|v y - v x| * |Y z - Y y|) := by
      rw [expansion_three_point, abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ 3 * ((V * pdist x y ^ (1 / 2 - 3 * κ)) *
        (H * pdist y z ^ (1 - 2 * κ))) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by
      have he : (3 / 2 - 5 * κ) - (1 / 2 - 3 * κ) = 1 - 2 * κ := by ring
      rw [he]
      ring

/-- A bounded smooth forcing pays precisely L^(2−γ) in the one-point
majorant; no derivative of the forcing appears. -/
theorem bounded_forcing_scale {T L β γ F : ℝ}
    (hT : 0 < T) (hTL : T ≤ L) (hβ : β ≤ 2) (hF : 0 ≤ F) :
    T ^ 2 * F ≤ F * T ^ β * L ^ (γ - β) * L ^ (2 - γ) := by
  have hL : 0 < L := hT.trans_le hTL
  have hpow := Real.rpow_le_rpow hT.le hTL (show 0 ≤ 2 - β by linarith)
  have heq : L ^ (γ - β) * L ^ (2 - γ) = L ^ (2 - β) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = F * T ^ β * T ^ (2 - β) := by
      rw [mul_assoc, ← Real.rpow_add hT]
      norm_num
      ring
    _ ≤ F * T ^ β * L ^ (2 - β) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hF (Real.rpow_nonneg hT.le _))
    _ = _ := by rw [mul_assoc (F * T ^ β), heq]

end GlobalPhi43.Local
