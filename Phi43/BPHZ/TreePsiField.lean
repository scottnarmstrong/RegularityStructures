/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiFubini
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import Phi43.Stochastic.ConstantsComparisonKernelLp

/-!
# The tree `Ψ`: the field `K ∗ ξ_ε` as a white-noise pairing

For a regularised noise `ξ` (a smooth version of `z ↦ W (ρ_ε^♯(z - ·))`) we define the pathwise
field `hairerPsiField N ξ ω z = ∫ K(z - w) ξ ω w dw` with Hairer's torus kernel `K`.  By stochastic
Fubini, for each `z` it is almost surely `W (K_ε(z - ·))` with `K_ε = hairerMollifiedKernel N ρ ε`,
and `E[Ψ(z) Ψ(z')] = Q_ε(z - z')` with `Q_ε = hairerCovariance N ρ ε` [Hai14, p. 166].

Convention: `K_ε(z) = ∫ K(z - w) ρ_ε^♯(w) dw` and `Q_ε(z) = ∫ K_ε(z + w) K_ε(w) dw`, so that
`∫ K_ε(z - w) K_ε(z' - w) dw = Q_ε(z - z')`; the covariance is evaluated at `z - z'`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The pathwise field `Ψ(z) = ∫ K(z - w) ξ(w) dw` for Hairer's periodised kernel `K`. -/
def hairerPsiField {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * ξ ω w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The reflected torus kernel is integrable. -/
theorem integrable_hairerKernelTorus_sub (N : ℕ) (z : SpaceTime) :
    Integrable (fun w => hairerKernelTorus N (z - w)) :=
  integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) z

/-- Pushing `K(z - ·)` through the mollifier family gives `K_ε(z - ·)`. -/
theorem treePsiConv_hairerKernelTorus (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z v : SpaceTime) :
    treePsiConv ρ ε (fun x => hairerKernelTorus N (z - x)) v =
      hairerMollifiedKernel N ρ ε (z - v) := by
  unfold treePsiConv hairerMollifiedKernel mollifierAt
  rw [← integral_comp_add_left_spaceTime
    (fun x => hairerKernelTorus N (z - x) * periodise ρ ε (x - v)) v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [sub_sub, add_sub_cancel_left]

/-- **The tree `Ψ` as a white-noise pairing.** For every `z`, almost surely
`Ψ(z) = W (K_ε(z - ·))`. -/
theorem hairerPsiField_ae_eq (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    (fun ω => hairerPsiField N ξ ω z) =ᵐ[P]
      W (fun w => hairerMollifiedKernel N ρ ε (z - w)) := by
  have h := treePsi_stochasticFubini_ae hρ hε hW hξ (integrable_hairerKernelTorus_sub N z)
  have hfun : treePsiConv ρ ε (fun x => hairerKernelTorus N (z - x)) =
      fun w => hairerMollifiedKernel N ρ ε (z - w) :=
    funext (treePsiConv_hairerKernelTorus N ρ ε z)
  rw [hfun] at h
  exact h

/-- `K_ε(z - ·)` is square integrable. -/
theorem memLp_hairerMollifiedKernel_sub (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (z : SpaceTime) : MemLp (fun w => hairerMollifiedKernel N ρ ε (z - w)) 2 := by
  have h := treePsi_memLp_conv hρ hε (integrable_hairerKernelTorus_sub N z)
  have hfun : treePsiConv ρ ε (fun x => hairerKernelTorus N (z - x)) =
      fun w => hairerMollifiedKernel N ρ ε (z - w) :=
    funext (treePsiConv_hairerKernelTorus N ρ ε z)
  rw [hfun] at h
  exact h

/-- `∫ K_ε(z - w) K_ε(z' - w) dw = Q_ε(z - z')`. -/
theorem integral_hairerMollifiedKernel_sub_mul (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z z' : SpaceTime) :
    ∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε (z' - w) =
      hairerCovariance N ρ ε (z - z') := by
  have h := integral_comp_sub_left_spaceTime
    (fun v => hairerMollifiedKernel N ρ ε (z - z' + v) * hairerMollifiedKernel N ρ ε v) z'
  simp only [sub_add_sub_cancel] at h
  rw [hairerCovariance, h]

/-- **Covariance of the tree `Ψ`.** `E[Ψ(z) Ψ(z')] = Q_ε(z - z')`. -/
theorem hairerPsiField_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (z z' : SpaceTime) :
    ∫ ω, hairerPsiField N ξ ω z * hairerPsiField N ξ ω z' ∂P =
      hairerCovariance N ρ ε (z - z') := by
  calc ∫ ω, hairerPsiField N ξ ω z * hairerPsiField N ξ ω z' ∂P
      = ∫ ω, W (fun w => hairerMollifiedKernel N ρ ε (z - w)) ω *
          W (fun w => hairerMollifiedKernel N ρ ε (z' - w)) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hairerPsiField_ae_eq N hρ hε hW hξ z,
          hairerPsiField_ae_eq N hρ hε hW hξ z'] with ω h1 h2
        rw [h1, h2]
    _ = ∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε (z' - w) :=
        whiteNoise_pairing_mul_integral hW (memLp_hairerMollifiedKernel_sub N hρ hε z)
          (memLp_hairerMollifiedKernel_sub N hρ hε z')
    _ = _ := integral_hairerMollifiedKernel_sub_mul N ρ ε z z'

/-- `Ψ(z)` is square integrable. -/
theorem hairerPsiField_memLp (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    MemLp (fun ω => hairerPsiField N ξ ω z) 2 P := by
  have hvec := hW.2 1 (fun _ => fun w => hairerMollifiedKernel N ρ ε (z - w))
    (fun _ => memLp_hairerMollifiedKernel_sub N hρ hε z)
  exact (memLp_congr_ae (hairerPsiField_ae_eq N hρ hε hW hξ z)).2 (hvec.memLp_two_apply 0)

end RegularityStructures.Phi43

end
