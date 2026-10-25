/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Parabolic geometry on `ℝ⁴ = ℝ × ℝ³`

Space-time `ℝ⁴` is the product `ℝ × (Fin 3 → ℝ)`, a time coordinate and three space coordinates,
with the parabolic scaling `𝔰 = (2, 1, 1, 1)`. We measure distances with the parabolic size
`‖z‖_𝔰 = |z₀|^{1/2} + |z₁| + |z₂| + |z₃|` of [Hos25, §2.1] (`‖x‖_s = ∑ᵢ |xᵢ|^{1/sᵢ}`), which is
comparable to Hairer's `|z|_𝔰 = |z₀|^{1/2} + |z'|` [Hai14, §2], and satisfies the triangle
inequality and exact scaling `‖(c² t, c x)‖_𝔰 = c ‖(t, x)‖_𝔰`.

Sources: [Hos25] = arXiv:2310.07396v2, §2.1; [Hai14] = arXiv:1303.5113v4, §2.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Space-time `ℝ⁴ = ℝ × ℝ³`, with time first. -/
abbrev ParabolicSpace : Type := ℝ × (Fin 3 → ℝ)

/-- The parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` for the scaling `𝔰 = (2, 1, 1, 1)`. -/
def parabolicNorm (z : ParabolicSpace) : ℝ := Real.sqrt |z.1| + ∑ i, |z.2 i|

/-- The parabolic dilation `S^c z = (c² z₀, c z')`. -/
def parabolicDilate (c : ℝ) (z : ParabolicSpace) : ParabolicSpace := (c ^ 2 * z.1, c • z.2)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem parabolicNorm_nonneg (z : ParabolicSpace) : 0 ≤ parabolicNorm z :=
  add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

@[simp]
theorem parabolicNorm_zero : parabolicNorm 0 = 0 := by
  simp [parabolicNorm]

theorem continuous_parabolicNorm : Continuous parabolicNorm := by
  unfold parabolicNorm
  fun_prop

theorem parabolicNorm_neg (z : ParabolicSpace) : parabolicNorm (-z) = parabolicNorm z := by
  simp [parabolicNorm, abs_neg]

theorem parabolicNorm_sub_comm (z w : ParabolicSpace) :
    parabolicNorm (z - w) = parabolicNorm (w - z) := by
  rw [← neg_sub, parabolicNorm_neg]

theorem sqrt_abs_add_le (a b : ℝ) : Real.sqrt |a + b| ≤ Real.sqrt |a| + Real.sqrt |b| := by
  rw [Real.sqrt_le_left (by positivity)]
  calc |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ (Real.sqrt |a| + Real.sqrt |b|) ^ 2 := by
      have ha := Real.sq_sqrt (abs_nonneg a)
      have hb := Real.sq_sqrt (abs_nonneg b)
      nlinarith [Real.sqrt_nonneg |a|, Real.sqrt_nonneg |b|]

/-- The triangle inequality for the parabolic size. -/
theorem parabolicNorm_add_le (z w : ParabolicSpace) :
    parabolicNorm (z + w) ≤ parabolicNorm z + parabolicNorm w := by
  unfold parabolicNorm
  have h1 := sqrt_abs_add_le z.1 w.1
  have h2 : ∑ i, |(z + w).2 i| ≤ ∑ i, |z.2 i| + ∑ i, |w.2 i| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => abs_add_le _ _
  simp only [Prod.fst_add] at h1 ⊢
  linarith

/-- Exact parabolic scaling: `‖S^c z‖_𝔰 = c ‖z‖_𝔰` for `c ≥ 0`. -/
theorem parabolicNorm_parabolicDilate {c : ℝ} (hc : 0 ≤ c) (z : ParabolicSpace) :
    parabolicNorm (parabolicDilate c z) = c * parabolicNorm z := by
  unfold parabolicNorm parabolicDilate
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  rw [abs_of_nonneg (sq_nonneg c), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc,
    ← Finset.mul_sum]
  ring

end RegularityStructures

end
