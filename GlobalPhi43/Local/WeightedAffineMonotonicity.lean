/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.WeightedAffineError

/-! Monotonicity in the actual affine-error radius cutoff, needed because
the scale recurrence and the causal embedding use different cutoffs. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

theorem weightedPastAffineError_mono_radius (U : GermPoint → ℝ)
    {r d₀ θ₁ θ₂ γ : ℝ} (hθ : θ₁ ≤ θ₂) :
    weightedPastAffineError U r d₀ θ₁ γ ≤ weightedPastAffineError U r d₀ θ₂ γ := by
  have hall : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ R ∈ Ioc (0 : ℝ) (θ₂ * d), ENNReal.ofReal (d ^ γ / R ^ γ) *
        pastAffineError (fun y => U (x, y)) x R ≤ weightedPastAffineError U r d₀ θ₂ γ := by
    simpa only [weightedPastAffineError, iSup_le_iff] using
      (le_rfl : weightedPastAffineError U r d₀ θ₂ γ ≤ weightedPastAffineError U r d₀ θ₂ γ)
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro R
  apply iSup_le
  intro hR
  exact hall d hd x hx R ⟨hR.1, hR.2.trans (mul_le_mul_of_nonneg_right hθ hd.1.le)⟩

end GlobalPhi43.Local
