/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Chaos1Cross
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Alg
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Point
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePieces

/-!
# The potential parts of the chaos-`1` difference of `I(Ψ³)Ψ²`, for arbitrary `u, u'`

Global versions of `i3Psi2HzDelta_le`, `chaosOne_diff_cross_bound`, `chaosOne_diff_pp_bound`: the
hypotheses `s(u), s(u') ≤ 1` (used to bound `s(u - w) ≤ 3` on the slab `|w.1| ≤ 1` carrying the
support of `K(-·)`, and to compare exponents) are replaced by a bound `s(u - w) ≤ D` for
`|w.1| ≤ 1`; `3^δ` becomes `D^δ`, and the exponents are not compared.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Majorant of `h^Δ_z`, for arbitrary `z`. -/
theorem i3Psi2HzDelta_le_global {K Qa Qb : SpaceTime → ℝ} {B μ θ ν D : ℝ} (hB : 0 ≤ B)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hD0 : 0 ≤ D) (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQa : ∀ x, 0 < torusParabolicSize x → |Qa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQb : ∀ x, 0 < torusParabolicSize x → |Qb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Qa x - Qb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ)))
    (hQae : ∀ x, Qa (-x) = Qa x) (hQbe : ∀ x, Qb (-x) = Qb x) {z : SpaceTime}
    (hD : ∀ w : SpaceTime, |w.1| ≤ 1 → torusParabolicSize (z - w) ≤ D)
    {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w))
    (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2HzDelta K Qa Qb z w ≤
      (2 * B ^ 3 * μ * D ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) := by
  have n3 : (0 : ℝ) ≤ D ^ ν := Real.rpow_nonneg hD0 _
  have hrhs : 0 ≤ (2 * B ^ 3 * μ * D ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) :=
    mul_nonneg (by positivity) (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 1
  · have a1 := hK (-w) (by simpa using h0)
    have e1 : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by simp [singularPow]
    have q1 : |Qa (w - z) - Qb (w - z)| ≤ B * μ * singularPow (1 + θ) z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      exact hΔ _ hzw
    have q2 : |Qa (w - z) + Qb (w - z)| ≤ 2 * B * singularPow 1 z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      have h1 := abs_add_le (Qa (z - w)) (Qb (z - w))
      have h2 := hQa (z - w) hzw
      have h3 := hQb (z - w) hzw
      unfold singularPow
      linarith
    have mul12 : singularPow (1 + θ) z w * singularPow 1 z w = singularPow (1 + θ + 1) z w :=
      singularPow_mul_self (1 + θ) 1 z w hzw
    have loss := singularPow_loss_le_of_le (p := 1 + θ + 1) hν hzw (hD w hw)
    have q3 : |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        2 * B ^ 2 * μ * (D ^ ν * singularPow (2 + θ + ν) z w) := by
      rw [show Qa (w - z) ^ 2 - Qb (w - z) ^ 2 = (Qa (w - z) - Qb (w - z)) *
        (Qa (w - z) + Qb (w - z)) by ring, abs_mul]
      calc |Qa (w - z) - Qb (w - z)| * |Qa (w - z) + Qb (w - z)|
          ≤ (B * μ * singularPow (1 + θ) z w) * (2 * B * singularPow 1 z w) :=
            mul_le_mul q1 q2 (abs_nonneg _) (mul_nonneg (mul_nonneg hB hμ)
              (singularPow_nonneg _ _ _))
        _ = 2 * B ^ 2 * μ * (singularPow (1 + θ) z w * singularPow 1 z w) := by ring
        _ = 2 * B ^ 2 * μ * singularPow (1 + θ + 1) z w := by rw [mul12]
        _ ≤ 2 * B ^ 2 * μ * (D ^ ν * singularPow (2 + θ + ν) z w) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have e : 1 + θ + 1 + ν = 2 + θ + ν := by ring
            rw [e] at loss
            exact loss
    unfold i3Psi2HzDelta
    rw [e1] at *
    calc |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        (B * torusParabolicSize (-w) ^ (-(3 : ℝ))) *
          (2 * B ^ 2 * μ * (D ^ ν * singularPow (2 + θ + ν) z w)) :=
          mul_le_mul a1 q3 (abs_nonneg _) (mul_nonneg hB (Real.rpow_nonneg
            (torusParabolicSize_nonneg _) _))
      _ = _ := by ring
  · have : K (-w) = 0 := by
      apply hKs
      have : (-w).1 = -w.1 := rfl
      rw [this, abs_neg]; exact not_le.1 hw
    unfold i3Psi2HzDelta
    rw [this]
    simpa using hrhs

end RegularityStructures

end
