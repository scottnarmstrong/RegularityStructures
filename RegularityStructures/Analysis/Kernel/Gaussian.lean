/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.SymbolScale

/-!
# The one-dimensional heat kernel

`heatKernel1D t b = symKernel 1 t b` is the inverse Fourier transform of `ξ ↦ exp(-t ξ^2)`,
`∫ exp(-t ξ^2) cos(2π ξ b) dξ`. It satisfies exact scaling with `t^{-1/2}`, has integral `1`,
the semigroup property and rapid decay of `heatKernel1D 1` and its derivative, and the scaled moment
formula. See `RegularityStructures.Analysis.Kernel.Symbol` and
`RegularityStructures.Analysis.Kernel.SymbolScale` for the proofs. This is the
temporal factor of the auxiliary semigroup of [Hos25, Example 2.7] (arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The one-dimensional heat kernel `𝓕⁻¹(ξ ↦ exp(-t ξ²)) = √(π/t) exp(-π² a²/t)` (variance proportional to `t`). -/
def heatKernel1D (t b : ℝ) : ℝ := symKernel 1 t b

/-- The moment `∫ |heatKernel1D 1 b| |b|^s db`. -/
def heatMoment (s : ℝ) : ℝ := ∫ b, |heatKernel1D 1 b| * |b| ^ s

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem heatKernel1D_eq_scale {t : ℝ} (ht : 0 < t) (b : ℝ) :
    heatKernel1D t b = t ^ (-(1 / (2 : ℝ))) * heatKernel1D 1 (t ^ (-(1 / (2 : ℝ))) * b) := by
  have := symKernel_eq_scale (j := 1) (by norm_num) ht b
  norm_num at this
  exact this

theorem integral_heatKernel1D {t : ℝ} (ht : 0 < t) : ∫ b, heatKernel1D t b = 1 :=
  integral_symKernel ht (by norm_num : 0 < 1)

theorem measurable_heatKernel1D (t : ℝ) : Measurable (heatKernel1D t) :=
  measurable_symKernel _ t

theorem heatKernel1D_neg (t b : ℝ) : heatKernel1D t (-b) = heatKernel1D t b :=
  symKernel_neg _ t b

theorem integral_heatKernel1D_mul_heatKernel1D {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a c : ℝ) :
    ∫ b, heatKernel1D s (a - b) * heatKernel1D t (b - c) = heatKernel1D (s + t) (a - c) :=
  integral_symKernel_mul_symKernel (by norm_num : 0 < 1) hs ht a c

theorem heatKernel1D_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |heatKernel1D 1 b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  symKernel_one_decay (by norm_num : 0 < 1) n

theorem differentiable_heatKernel1D_one : Differentiable ℝ (heatKernel1D 1) :=
  differentiable_symKernel_one (by norm_num : 0 < 1)

theorem deriv_heatKernel1D_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |deriv (heatKernel1D 1) b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  deriv_symKernel_one_decay (by norm_num : 0 < 1) n

theorem integrable_abs_heatKernel1D_mul_rpow {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun b => |heatKernel1D t b| * |b| ^ s) :=
  integrable_abs_symKernel_mul_rpow (by norm_num : 0 < 1) ht hs

/-- Scaling of the moments: `∫ |heatKernel1D t b| |b|^s db = t^{s/2} heatMoment s`. -/
theorem integral_abs_heatKernel1D_mul_rpow {t : ℝ} (ht : 0 < t) (s : ℝ) :
    ∫ b, |heatKernel1D t b| * |b| ^ s = t ^ (s / (2 : ℝ)) * heatMoment s := by
  have := integral_abs_symKernel_mul_rpow (j := 1) (by norm_num) ht s
  norm_num at this
  exact this

theorem heatMoment_nonneg (s : ℝ) : 0 ≤ heatMoment s :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)

end RegularityStructures

end
