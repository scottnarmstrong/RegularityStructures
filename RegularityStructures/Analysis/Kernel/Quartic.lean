/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.SymbolScale

/-!
# The quartic kernel

`quarticKernel t b = symKernel 2 t b` is the inverse Fourier transform of `ξ ↦ exp(-t ξ^4)`,
`∫ exp(-t ξ^4) cos(2π ξ b) dξ`. It satisfies exact scaling with `t^{-1/4}`, has integral `1`,
the semigroup property and rapid decay of `quarticKernel 1` and its derivative, and the scaled moment
formula. See `RegularityStructures.Analysis.Kernel.Symbol` and
`RegularityStructures.Analysis.Kernel.SymbolScale` for the proofs. This is the
spatial factor of the auxiliary semigroup of [Hos25, Example 2.7] (arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The one-dimensional quartic kernel `𝓕⁻¹(ξ ↦ exp(-t ξ⁴))` (fundamental solution of `∂_t + ∂_b⁴`). -/
def quarticKernel (t b : ℝ) : ℝ := symKernel 2 t b

/-- The moment `∫ |quarticKernel 1 b| |b|^s db`. -/
def quarticMoment (s : ℝ) : ℝ := ∫ b, |quarticKernel 1 b| * |b| ^ s

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem quarticKernel_eq_scale {t : ℝ} (ht : 0 < t) (b : ℝ) :
    quarticKernel t b = t ^ (-(1 / (4 : ℝ))) * quarticKernel 1 (t ^ (-(1 / (4 : ℝ))) * b) := by
  have := symKernel_eq_scale (j := 2) (by norm_num) ht b
  norm_num at this
  exact this

theorem integral_quarticKernel {t : ℝ} (ht : 0 < t) : ∫ b, quarticKernel t b = 1 :=
  integral_symKernel ht (by norm_num : 0 < 2)

theorem measurable_quarticKernel (t : ℝ) : Measurable (quarticKernel t) :=
  measurable_symKernel _ t

theorem quarticKernel_neg (t b : ℝ) : quarticKernel t (-b) = quarticKernel t b :=
  symKernel_neg _ t b

theorem integral_quarticKernel_mul_quarticKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a c : ℝ) :
    ∫ b, quarticKernel s (a - b) * quarticKernel t (b - c) = quarticKernel (s + t) (a - c) :=
  integral_symKernel_mul_symKernel (by norm_num : 0 < 2) hs ht a c

theorem quarticKernel_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |quarticKernel 1 b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  symKernel_one_decay (by norm_num : 0 < 2) n

theorem differentiable_quarticKernel_one : Differentiable ℝ (quarticKernel 1) :=
  differentiable_symKernel_one (by norm_num : 0 < 2)

theorem deriv_quarticKernel_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |deriv (quarticKernel 1) b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  deriv_symKernel_one_decay (by norm_num : 0 < 2) n

theorem integrable_abs_quarticKernel_mul_rpow {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun b => |quarticKernel t b| * |b| ^ s) :=
  integrable_abs_symKernel_mul_rpow (by norm_num : 0 < 2) ht hs

/-- Scaling of the moments: `∫ |quarticKernel t b| |b|^s db = t^{s/4} quarticMoment s`. -/
theorem integral_abs_quarticKernel_mul_rpow {t : ℝ} (ht : 0 < t) (s : ℝ) :
    ∫ b, |quarticKernel t b| * |b| ^ s = t ^ (s / (4 : ℝ)) * quarticMoment s := by
  have := integral_abs_symKernel_mul_rpow (j := 2) (by norm_num) ht s
  norm_num at this
  exact this

theorem quarticMoment_nonneg (s : ℝ) : 0 ≤ quarticMoment s :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)

end RegularityStructures

end
