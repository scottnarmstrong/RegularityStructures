/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FutureRemainder

/-! The past coordinate probes used in the radius-local Schauder estimate. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped BigOperators

/-- Move one spatial coordinate by s and time backwards by s². -/
def coefficientProbe (x : ParabolicSpace) (s : ℝ) (i : Fin 3) : ParabolicSpace :=
  (x.1 - s ^ 2, x.2 + Pi.single i s)

theorem coefficientProbe_distance (x : ParabolicSpace) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 3) : pdist x (coefficientProbe x s i) = s := by
  have ht : x.1 - (x.1 - s ^ 2) = s ^ 2 := by ring
  have hx : x.2 - (x.2 + Pi.single i s) = -Pi.single i s := by abel
  change max (Real.sqrt |x.1 - (x.1 - s ^ 2)|) ‖x.2 - (x.2 + Pi.single i s)‖ = s
  rw [ht, hx, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq hs,
    norm_neg, Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg hs, max_self]

theorem coefficientProbe_past {x : ParabolicSpace} {s L : ℝ} (hs : 0 < s)
    (hsL : s < L) (i : Fin 3) : coefficientProbe x s i ∈ pastBall x L := by
  exact ⟨by rw [coefficientProbe_distance x hs.le]; exact hsL,
    by change x.1 - s ^ 2 < x.1; nlinarith [sq_pos_of_pos hs]⟩

/-- The exact loss is s, including at a probe at distance exactly s. -/
theorem coefficientProbe_interior {r d s : ℝ} {x : ParabolicSpace}
    (hs : 0 ≤ s) (hsd : s ≤ d) (hx : x ∈ cylinderInterior r d) (i : Fin 3) :
    coefficientProbe x s i ∈ cylinderInterior r (d - s) := by
  refine ⟨?_, ?_, fun j => ?_⟩
  · change r ^ 2 + (d - s) ^ 2 < x.1 - s ^ 2
    nlinarith [hx.1, mul_nonneg hs (sub_nonneg.mpr hsd)]
  · change x.1 - s ^ 2 < 1
    nlinarith [hx.2.1, sq_nonneg s]
  · have hj : |(Pi.single i s : Fin 3 → ℝ) j| ≤ s := by
      by_cases h : j = i
      · subst j; simp [abs_of_nonneg hs]
      · simp [h, hs]
    obtain ⟨hl, hu⟩ := hx.2.2 j
    have hb := abs_le.mp hj
    change -1 + r + (d - s) < x.2 j + (Pi.single i s : Fin 3 → ℝ) j ∧
      x.2 j + (Pi.single i s : Fin 3 → ℝ) j < 1 - r - (d - s)
    constructor <;> linarith

theorem spatialLinear_coefficientProbe (ν : Fin 3 → ℝ) (x : ParabolicSpace)
    (s : ℝ) (i : Fin 3) : spatialLinear ν (coefficientProbe x s i - x) = s * ν i := by
  simp only [spatialLinear, coefficientProbe, Prod.snd_sub, Pi.sub_apply, Pi.add_apply,
    add_sub_cancel_left]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [hji]
  · simp

/-- One probe determines a coordinate without a derivative norm of ν. -/
theorem coefficient_bound_from_probe
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x : ParabolicSpace) (i : Fin 3) {s B Q γ : ℝ} (hs : 0 < s)
    (hU : |U x (coefficientProbe x s i)| ≤ B)
    (hR : |affineRemainder U ν x (coefficientProbe x s i)| ≤ Q * s ^ γ) :
    |ν x i| ≤ (B + Q * s ^ γ) / s := by
  have he : s * ν x i = U x (coefficientProbe x s i) -
      affineRemainder U ν x (coefficientProbe x s i) := by
    rw [affineRemainder, spatialLinear_coefficientProbe]
    ring
  apply (le_div_iff₀ hs).2
  calc
    |ν x i| * s = |s * ν x i| := by rw [abs_mul, abs_of_pos hs]; ring
    _ ≤ |U x (coefficientProbe x s i)| +
        |affineRemainder U ν x (coefficientProbe x s i)| := by rw [he]; exact abs_sub _ _
    _ ≤ B + Q * s ^ γ := add_le_add hU hR

end GlobalPhi43.Local
