/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullKernels
import Mathlib.Tactic

/-!
# `g_i` and `v₁` at large distances

With `T₀(z) = (K ∗ Ψ)(z)` (`gammaFullConv`) and `Tᵢ(z) = ∂ᵢ(K ∗ Ψ)(z)` (`gammaFullGrad`), pathwise
* `gammaGrad N ξ i x y = Tᵢ(y) - Tᵢ(x)`,
* `gammaPsiTaylor N ξ x t a = T₀(x + (t, proj a)) - T₀(x) - ∑ᵢ aᵢ Tᵢ(x)`.

Minkowski with the uniform moments of `GammaFullKernels` gives, for all `x, y` and all `(t, a)`,
`∫⁻ ‖g_i‖ₑ^q ≤ ofReal C ^ q` and `∫⁻ ‖v₁‖ₑ^q ≤ ofReal (C (1 + r))^q` when all `|aᵢ| ≤ r`, and the
same for the two-scale differences with the factor `(ε ∨ ε')^θ`.
-/

@[expose] public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `T₀(z) = (K ∗ Ψ)(z)` for the periodised Hairer kernel. -/
noncomputable def gammaFullConv {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (z : SpaceTime)
    (ω : Ω) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * hairerPsiField N ξ ω w

/-- `Tᵢ(z) = ∂ᵢ(K ∗ Ψ)(z)` for the periodised gradient kernel. -/
noncomputable def gammaFullGrad {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (i : Fin 3)
    (z : SpaceTime) (ω : Ω) : ℝ :=
  ∫ w, hairerKernelTorusGrad N i (z - w) * hairerPsiField N ξ ω w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} {N : ℕ} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}

theorem gammaGrad_eq_gammaFullGrad_sub (hξ : IsSmoothOnSpaceTime (ξ ω)) (i : Fin 3)
    (x y : SpaceTime) :
    gammaGrad N ξ i x y ω = gammaFullGrad N ξ i y ω - gammaFullGrad N ξ i x ω := by
  have hc : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  unfold gammaGrad gammaFullGrad
  rw [← integral_sub (integrable_hairerKernelTorusGrad_sub_mul_continuous N i y hc)
    (integrable_hairerKernelTorusGrad_sub_mul_continuous N i x hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hairerGradIncrementKernel]
  ring

theorem gammaPsiTaylor_eq_gammaFullConv_sub (hξ : IsSmoothOnSpaceTime (ξ ω)) (x : SpaceTime) (t : ℝ)
    (a : Fin 3 → ℝ) :
    gammaPsiTaylor N ξ x t a ω = gammaFullConv N ξ (x + (t, torusProj a)) ω - gammaFullConv N ξ x ω -
      ∑ i : Fin 3, a i * gammaFullGrad N ξ i x ω := by
  have hc : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  have i1 := integrable_hairerKernelTorus_sub_mul_continuous N (x + (t, torusProj a)) hc
  have i2 := integrable_hairerKernelTorus_sub_mul_continuous N x hc
  have i3 : ∀ i : Fin 3, Integrable (fun w => a i *
      (hairerKernelTorusGrad N i (x - w) * hairerPsiField N ξ ω w)) := fun i =>
    (integrable_hairerKernelTorusGrad_sub_mul_continuous N i x hc).const_mul _
  unfold gammaPsiTaylor gammaFullConv gammaFullGrad
  have e : ∀ w, hairerTaylorKernel N x t a w * hairerPsiField N ξ ω w =
      hairerKernelTorus N (x + (t, torusProj a) - w) * hairerPsiField N ξ ω w -
        hairerKernelTorus N (x - w) * hairerPsiField N ξ ω w -
        ∑ i : Fin 3, a i * (hairerKernelTorusGrad N i (x - w) * hairerPsiField N ξ ω w) := by
    intro w
    unfold hairerTaylorKernel
    rw [sub_mul, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [e]
  have iS : Integrable (fun w => ∑ i : Fin 3, a i *
      (hairerKernelTorusGrad N i (x - w) * hairerPsiField N ξ ω w)) :=
    integrable_finsetSum _ fun i _ => i3 i
  have iA : Integrable (fun w => hairerKernelTorus N (x + (t, torusProj a) - w) *
      hairerPsiField N ξ ω w - hairerKernelTorus N (x - w) * hairerPsiField N ξ ω w) := i1.sub i2
  rw [integral_sub iA iS, integral_sub i1 i2, integral_finsetSum _ fun i _ => i3 i]
  simp_rw [integral_const_mul]

end RegularityStructures.Phi43

end
