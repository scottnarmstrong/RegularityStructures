/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.SymbolScale

/-!
# The time derivative of the symbol kernels

From exact scaling `k_t(b) = λ k_1(λ b)`, `λ = t^{-1/(2j)}`, we obtain, for `t > 0`,
`∂_t k_t(b) = -(1/(2j t)) λ (k_1(u) + u k_1'(u))` with `u = λ b`, with no PDE needed. This is the
1D input of the time-derivative bound [Hos25, Definition 2.6 (iv)] (arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The scale `t^{-1/(2j)}` of `symKernel j t`. -/
def symScale (j : ℕ) (t : ℝ) : ℝ := t ^ (-(1 / ((2 * j : ℕ) : ℝ)))

/-- The profile `φ(u) = k_1(u) + u k_1'(u)` in `∂_t k_t(b) = -(1/(2j t)) λ φ(λ b)`. -/
def symProfile (j : ℕ) (u : ℝ) : ℝ := symKernel j 1 u + u * deriv (symKernel j 1) u

/-- The time derivative of `t ↦ symKernel j t b`. -/
def symKernelTimeDeriv (j : ℕ) (t b : ℝ) : ℝ :=
  -(1 / ((2 * j : ℕ) : ℝ)) * t⁻¹ * symScale j t * symProfile j (symScale j t * b)

end RegularityStructures

end

public section

open MeasureTheory Real

namespace RegularityStructures

variable {j : ℕ} (hj : 0 < j)

theorem symScale_pos {t : ℝ} (ht : 0 < t) (j : ℕ) : 0 < symScale j t :=
  Real.rpow_pos_of_pos ht _

include hj in
theorem hasDerivAt_symKernel_time {t : ℝ} (ht : 0 < t) (b : ℝ) :
    HasDerivAt (fun s => symKernel j s b) (symKernelTimeDeriv j t b) t := by
  set a : ℝ := 1 / ((2 * j : ℕ) : ℝ) with ha
  have hl : HasDerivAt (fun s : ℝ => s ^ (-a)) (-a * t ^ (-a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hu : HasDerivAt (fun s : ℝ => s ^ (-a) * b) (-a * t ^ (-a - 1) * b) t := hl.mul_const b
  have hk := (differentiable_symKernel_one hj (t ^ (-a) * b)).hasDerivAt
  have hc := hk.comp t hu
  have hm := hl.mul hc
  have heq : (fun s => symKernel j s b) =ᶠ[nhds t]
      fun s => s ^ (-a) * (symKernel j 1 ∘ fun s : ℝ => s ^ (-a) * b) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact symKernel_eq_scale hj hs b
  refine (hm.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold symKernelTimeDeriv symProfile symScale
  rw [← ha, Real.rpow_sub_one ht.ne']
  simp only [Function.comp_apply]
  field_simp
  ring

include hj in
theorem abs_symKernelTimeDeriv_le {t : ℝ} (ht : 0 < t) (b : ℝ) :
    |symKernelTimeDeriv j t b| ≤
      (1 / ((2 * j : ℕ) : ℝ)) * t⁻¹ * symScale j t * |symProfile j (symScale j t * b)| := by
  unfold symKernelTimeDeriv
  have hl := symScale_pos ht j
  have hm : (0 : ℝ) < ((2 * j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * j)
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / ((2 * j : ℕ) : ℝ)),
    abs_of_pos (inv_pos.2 ht), abs_of_pos hl]

include hj in
/-- Rapid decay of the profile `k_1 + u k_1'`. -/
theorem symProfile_decay (n : ℕ) :
    ∃ C : ℝ, ∀ u, |symProfile j u| ≤ C * (1 + |u|) ^ (-(n : ℝ)) := by
  obtain ⟨C₁, h₁⟩ := symKernel_one_decay hj n
  obtain ⟨C₂, h₂⟩ := deriv_symKernel_one_decay hj (n + 1)
  refine ⟨C₁ + C₂, fun u => ?_⟩
  have hb : 0 < 1 + |u| := by positivity
  have h3 : |u| * |deriv (symKernel j 1) u| ≤ C₂ * (1 + |u|) ^ (-(n : ℝ)) := by
    have e : (1 + |u|) ^ (-((n + 1 : ℕ) : ℝ)) * (1 + |u|) = (1 + |u|) ^ (-(n : ℝ)) := by
      rw [show -((n + 1 : ℕ) : ℝ) = -(n : ℝ) - 1 by push_cast; ring, Real.rpow_sub_one hb.ne']
      field_simp
    calc |u| * |deriv (symKernel j 1) u| ≤ (1 + |u|) * (C₂ * (1 + |u|) ^ (-((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul (by linarith) (h₂ u) (abs_nonneg _) hb.le
      _ = C₂ * ((1 + |u|) ^ (-((n + 1 : ℕ) : ℝ)) * (1 + |u|)) := by ring
      _ = _ := by rw [e]
  unfold symProfile
  calc |symKernel j 1 u + u * deriv (symKernel j 1) u|
      ≤ |symKernel j 1 u| + |u * deriv (symKernel j 1) u| := abs_add_le _ _
    _ ≤ C₁ * (1 + |u|) ^ (-(n : ℝ)) + C₂ * (1 + |u|) ^ (-(n : ℝ)) := by
        rw [abs_mul]
        exact add_le_add (h₁ u) h3
    _ = _ := by ring

end RegularityStructures

end
