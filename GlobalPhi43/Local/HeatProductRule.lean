/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SecondDerivativeProduct
public import GlobalPhi43.MW20.HeatFrechet
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! Exact cutoff product rule for the actual coordinate heat operator. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20
open scoped ContDiff

 theorem sourceHeat_product {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (p : ParabolicSpace) :
    sourceHeat (fun q => f q * g q) p = f p * sourceHeat g p + g p * sourceHeat f p -
      2 * ∑ i : Fin 3, fderiv ℝ f p (0, Pi.single i 1) * fderiv ℝ g p (0, Pi.single i 1) := by
  have htF : DifferentiableAt ℝ (fun t : ℝ => f (t, p.2)) p.1 :=
    (hf.differentiable (by simp) p).comp p.1 ((differentiableAt_id).prodMk (differentiableAt_const p.2))
  have htG : DifferentiableAt ℝ (fun t : ℝ => g (t, p.2)) p.1 :=
    (hg.differentiable (by simp) p).comp p.1 ((differentiableAt_id).prodMk (differentiableAt_const p.2))
  have hsF (i : Fin 3) : ContDiff ℝ ∞ (fun a : ℝ => f (p.1, Function.update p.2 i a)) :=
    hf.comp (contDiff_const.prodMk (contDiff_update ∞ p.2 i))
  have hsG (i : Fin 3) : ContDiff ℝ ∞ (fun a : ℝ => g (p.1, Function.update p.2 i a)) :=
    hg.comp (contDiff_const.prodMk (contDiff_update ∞ p.2 i))
  have hsecond (i : Fin 3) :
      deriv (deriv (fun a : ℝ => f (p.1, Function.update p.2 i a) * g (p.1, Function.update p.2 i a))) (p.2 i) =
        deriv (deriv (fun a : ℝ => f (p.1, Function.update p.2 i a))) (p.2 i) * g p +
        2 * fderiv ℝ f p (0, Pi.single i 1) * fderiv ℝ g p (0, Pi.single i 1) +
        f p * deriv (deriv (fun a : ℝ => g (p.1, Function.update p.2 i a))) (p.2 i) := by
    rw [second_derivative_product (hsF i) (hsG i)]
    simp only [Function.update_eq_self]
    rw [source_space_deriv_eq_fderiv f p (hf.differentiable (by simp) p),
      source_space_deriv_eq_fderiv g p (hg.differentiable (by simp) p)]
  have htime : deriv (fun t : ℝ => f (t, p.2) * g (t, p.2)) p.1 =
      deriv (fun t : ℝ => f (t, p.2)) p.1 * g p + f p * deriv (fun t : ℝ => g (t, p.2)) p.1 :=
    deriv_mul htF htG
  unfold sourceHeat
  dsimp only
  rw [htime]
  simp_rw [hsecond]
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end GlobalPhi43.Local
