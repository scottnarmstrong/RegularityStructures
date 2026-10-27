/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusSourceSize
public import GlobalPhi43.Local.WeightedAffineExtraction

/-! The large-radius part of the scale argument uses the original radius-local U
budget at a shallower inset. The small-radius recurrence is kept explicit. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

/-- A past ball of radius at most d/2 is controlled by the literal B_U:
use the common inset d-R, rather than assuming its points belong to D_d. -/
theorem radiusSourceUSup_past_bound (U : GermPoint → ℝ) {r d₀ d R : ℝ}
    (hfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hR : 0 ≤ R) (hRd : R ≤ d / 2) {x y : ParabolicSpace}
    (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x R) :
    |U (x, y)| ≤ (radiusSourceUSup U r d₀).toReal := by
  have hs : 0 < d - R := by linarith [hd.1]
  apply radiusSourceUSup_bound U hfinite (d := d - R) ⟨hs, by linarith [hd.2]⟩
    (cylinderInterior_mono hs.le (by linarith) hx)
    (pastBall_subset_interior hs.le hR (by linarith) hx hy)
  exact hy.1.le.trans (by linarith)

/-- Choosing the zero affine map gives the actual affine-infimum bound;
no coefficient or affine minimizer is selected. -/
theorem pastAffineError_le_radiusSourceUSup (U : GermPoint → ℝ) {r d₀ d R : ℝ}
    (hfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hR : 0 ≤ R) (hRd : R ≤ d / 2) {x : ParabolicSpace}
    (hx : x ∈ cylinderInterior r d) :
    pastAffineError (fun y => U (x, y)) x R ≤ radiusSourceUSup U r d₀ := by
  apply iInf_le_of_le (0 : ℝ)
  apply iInf_le_of_le (0 : Fin 3 → ℝ)
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hb := radiusSourceUSup_past_bound U hfinite hd hR hRd hx hy
  have hz : spatialAffine x 0 (0 : Fin 3 → ℝ) y = 0 := by
    simp [spatialAffine, spatialLinear]
  simpa only [hz, sub_zero, ENNReal.ofReal_toReal hfinite] using ENNReal.ofReal_le_ofReal hb

/-- Exact large-scale normalization. The bound is uniform in d and R. -/
theorem large_affine_scale_bound (U : GermPoint → ℝ) {r d₀ d R ε γ : ℝ}
    (hfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hε : 0 < ε) (hγ : 0 ≤ γ) (hR : 0 < R) (hRd : R ≤ d / 2)
    (hlarge : ε * d / 8 ≤ R) {x : ParabolicSpace}
    (hx : x ∈ cylinderInterior r d) :
    ENNReal.ofReal (d ^ γ / R ^ γ) * pastAffineError (fun y => U (x, y)) x R ≤
      ENNReal.ofReal ((8 / ε) ^ γ * (radiusSourceUSup U r d₀).toReal) := by
  have hratio : d / R ≤ 8 / ε := by
    apply (div_le_div_iff₀ hR hε).2
    nlinarith
  have hpower : d ^ γ / R ^ γ ≤ (8 / ε) ^ γ := by
    rw [← Real.div_rpow hd.1.le hR.le]
    exact Real.rpow_le_rpow (div_nonneg hd.1.le hR.le) hratio hγ
  calc
    _ ≤ ENNReal.ofReal (d ^ γ / R ^ γ) * radiusSourceUSup U r d₀ := by
      gcongr
      exact pastAffineError_le_radiusSourceUSup U hfinite hd hR.le hRd hx
    _ = ENNReal.ofReal ((d ^ γ / R ^ γ) * (radiusSourceUSup U r d₀).toReal) := by
      rw [ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hd.1.le _) (Real.rpow_nonneg hR.le _)), ENNReal.ofReal_toReal hfinite]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpower ENNReal.toReal_nonneg)

/-- Split the actual scale supremum at epsilon*d/8. Its large-radius part
is paid by B_U; only the genuine small-radius estimate remains an input. -/
theorem weightedPastAffineError_scale_split (U : GermPoint → ℝ) {r d₀ θ ε γ H : ℝ}
    (hfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hθ : θ ≤ 1 / 2)
    (hε : 0 < ε) (hγ : 0 ≤ γ)
    (hsmall : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ R ∈ Ioc (0 : ℝ) (θ * d), R ≤ ε * d / 8 →
      ENNReal.ofReal (d ^ γ / R ^ γ) * pastAffineError (fun y => U (x, y)) x R ≤ ENNReal.ofReal H) :
    weightedPastAffineError U r d₀ θ γ ≤
      ENNReal.ofReal (max H ((8 / ε) ^ γ * (radiusSourceUSup U r d₀).toReal)) := by
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
  by_cases hs : R ≤ ε * d / 8
  · exact (hsmall d hd x hx R hR hs).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hRd : R ≤ d / 2 := hR.2.trans (by nlinarith [hd.1])
    exact (large_affine_scale_bound U hfinite hd hε hγ hR.1 hRd (le_of_not_ge hs) hx).trans
      (ENNReal.ofReal_le_ofReal (le_max_right _ _))

end GlobalPhi43.Local
