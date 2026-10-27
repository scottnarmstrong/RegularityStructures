/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CoefficientProbe

/-! Recover differences of affine coefficients from approximation errors on
strictly past probes; the intercept cancels between the two probes. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set

/-- The probe with no spatial displacement, at the same time as the coordinate probes. -/
def verticalProbe (x : ParabolicSpace) (s : ℝ) : ParabolicSpace := (x.1 - s ^ 2, x.2)

def spatialAffine (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ)
    (y : ParabolicSpace) : ℝ := c + spatialLinear ν (y - x)

theorem verticalProbe_distance (x : ParabolicSpace) {s : ℝ} (hs : 0 ≤ s) :
    pdist x (verticalProbe x s) = s := by
  have ht : x.1 - (x.1 - s ^ 2) = s ^ 2 := by ring
  change max (Real.sqrt |x.1 - (x.1 - s ^ 2)|) ‖x.2 - x.2‖ = s
  rw [ht, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq hs, sub_self, norm_zero,
    max_eq_left hs]

theorem verticalProbe_past {x : ParabolicSpace} {s L : ℝ} (hs : 0 < s)
    (hsL : s < L) : verticalProbe x s ∈ pastBall x L := by
  exact ⟨by rw [verticalProbe_distance x hs.le]; exact hsL,
    by change x.1 - s ^ 2 < x.1; nlinarith [sq_pos_of_pos hs]⟩

theorem spatialAffine_probe_difference (x : ParabolicSpace) (c : ℝ)
    (ν : Fin 3 → ℝ) (s : ℝ) (i : Fin 3) :
    spatialAffine x c ν (coefficientProbe x s i) - spatialAffine x c ν (verticalProbe x s) =
      s * ν i := by
  have hz : spatialLinear ν (verticalProbe x s - x) = 0 := by
    simp [spatialLinear, verticalProbe]
  simp only [spatialAffine, spatialLinear_coefficientProbe, hz]
  ring

/-- Two approximants on a common past ball have close spatial coefficients.
Both probes are strictly in the past; no value at the ball centre is used. -/
theorem affine_coefficients_compare (f : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (c₁ c₂ : ℝ) (ν₁ ν₂ : Fin 3 → ℝ)
    {s L E₁ E₂ : ℝ} (hs : 0 < s) (hsL : s < L)
    (h₁ : ∀ y ∈ pastBall x L, |f y - spatialAffine x c₁ ν₁ y| ≤ E₁)
    (h₂ : ∀ y ∈ pastBall x L, |f y - spatialAffine x c₂ ν₂ y| ≤ E₂) (i : Fin 3) :
    |ν₁ i - ν₂ i| ≤ 2 * (E₁ + E₂) / s := by
  have hcompare (y : ParabolicSpace) (hy : y ∈ pastBall x L) :
      |spatialAffine x c₁ ν₁ y - spatialAffine x c₂ ν₂ y| ≤ E₁ + E₂ := by
    calc
      _ = |(f y - spatialAffine x c₂ ν₂ y) - (f y - spatialAffine x c₁ ν₁ y)| := by
        congr 1; ring
      _ ≤ |f y - spatialAffine x c₂ ν₂ y| + |f y - spatialAffine x c₁ ν₁ y| := abs_sub _ _
      _ ≤ E₁ + E₂ := by linarith [h₁ y hy, h₂ y hy]
  have hi := hcompare (coefficientProbe x s i) (coefficientProbe_past hs hsL i)
  have hzero := hcompare (verticalProbe x s) (verticalProbe_past hs hsL)
  have hid : s * (ν₁ i - ν₂ i) =
      (spatialAffine x c₁ ν₁ (coefficientProbe x s i) -
        spatialAffine x c₂ ν₂ (coefficientProbe x s i)) -
      (spatialAffine x c₁ ν₁ (verticalProbe x s) -
        spatialAffine x c₂ ν₂ (verticalProbe x s)) := by
    have hfirst := spatialAffine_probe_difference x c₁ ν₁ s i
    have hsecond := spatialAffine_probe_difference x c₂ ν₂ s i
    linarith
  apply (le_div_iff₀ hs).2
  calc
    |ν₁ i - ν₂ i| * s = |s * (ν₁ i - ν₂ i)| := by rw [abs_mul, abs_of_pos hs]; ring
    _ ≤ 2 * (E₁ + E₂) := by
      rw [hid]
      exact (abs_sub _ _).trans (by linarith)

end GlobalPhi43.Local
