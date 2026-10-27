/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring

/-! The exact scalar second-derivative product rule for heat localization. -/
public noncomputable section

namespace GlobalPhi43.Local

open scoped ContDiff

 theorem second_derivative_product {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (deriv (fun r => f r * g r)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have hf' : Differentiable ℝ (deriv f) :=
    (show ContDiff ℝ 2 f from hf.of_le (by norm_num)).differentiable_deriv_two
  have hg' : Differentiable ℝ (deriv g) :=
    (show ContDiff ℝ 2 g from hg.of_le (by norm_num)).differentiable_deriv_two
  have hfd := hf.differentiable (by simp)
  have hgd := hg.differentiable (by simp)
  have he : deriv (fun r => f r * g r) = fun r => deriv f r * g r + f r * deriv g r :=
    funext fun r => deriv_mul (hfd r) (hgd r)
  rw [he]
  change deriv (deriv f * g + f * deriv g) x = _
  rw [deriv_add ((hf' x).mul (hgd x)) ((hfd x).mul (hg' x)),
    deriv_mul (hf' x) (hgd x), deriv_mul (hfd x) (hg' x)]
  ring

end GlobalPhi43.Local
