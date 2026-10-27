/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineScaleSplit
public import GlobalPhi43.Local.SmallPastSeminorm

/-! Taking the actual scale supremum using the local small-radius estimate. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

/-- The recurrence for the actual finite real quantities follows from the
normalized local inequality and the original B_U large-scale allowance. -/
theorem actual_scale_recurrence (U : GermPoint → ℝ) {r d₀ θ η ε γ a b P : ℝ}
    (hBfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hθ : θ ≤ 1 / 2)
    (hε : 0 < ε) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hsmall : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ R ∈ Ioc (0 : ℝ) (θ * d), R ≤ ε * d / 8 →
      ENNReal.ofReal (d ^ γ / R ^ γ) * pastAffineError (fun y => U (x, y)) x R ≤
        ENNReal.ofReal (a * (weightedPastAffineError U r d₀ θ γ).toReal + P +
          b * (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal)) :
    (weightedPastAffineError U r d₀ θ γ).toReal ≤
      a * (weightedPastAffineError U r d₀ θ γ).toReal +
      (P + (8 / ε) ^ γ * (radiusSourceUSup U r d₀).toReal) +
      b * (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal := by
  have hnorm := weightedPastAffineError_scale_split U hBfinite hθ hε hγ hsmall
  have hleft : 0 ≤ a * (weightedPastAffineError U r d₀ θ γ).toReal + P +
      b * (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ).toReal := by
    positivity
  have hright : 0 ≤ (8 / ε) ^ γ * (radiusSourceUSup U r d₀).toReal := by positivity
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (le_trans hleft (le_max_left _ _))] at hbound
  have hmax := max_le (le_add_of_nonneg_right hright) (le_add_of_nonneg_left hleft)
  have hout := hbound.trans hmax
  nlinarith only [hout]

end GlobalPhi43.Local
