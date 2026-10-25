/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldDifference
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.PsiGaussianVector

/-!
# The covariance of the field of `I(Ψ³)Ψ²` as the abstract diagram

For the base point `x` and the points `y, ȳ`, `hairerI3Psi2Cov N ρ x ε ε y ȳ` equals
`i3Psi2Cov K Q c (y - x) (ȳ - x)` with `K = hairerKernelTorus N`, `Q = hairerCovariance N ρ ε`,
`c = hairerSunsetConstant N ρ ε`: translate the integration variables by `x`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (x y y' : SpaceTime)

private theorem integral_prod_translate (F : SpaceTime × SpaceTime → ℝ) :
    ∫ q : SpaceTime × SpaceTime, F q = ∫ q : SpaceTime × SpaceTime, F (x + q.1, x + q.2) := by
  have hmp : MeasurePreserving (fun q : SpaceTime × SpaceTime => (x + q.1, x + q.2))
      ((volume : Measure SpaceTime).prod volume) ((volume : Measure SpaceTime).prod volume) :=
    (measurePreserving_add_left volume x).prod (measurePreserving_add_left volume x)
  exact (hmp.integral_comp (MeasurableEquiv.prodCongr (MeasurableEquiv.addLeft x)
    (MeasurableEquiv.addLeft x)).measurableEmbedding F).symm

private theorem integral_translate (F : SpaceTime → ℝ) :
    ∫ w : SpaceTime, F w = ∫ a : SpaceTime, F (x + a) :=
  (integral_add_left_eq_self F x).symm

private theorem kernel_translate (a : SpaceTime) :
    hairerI2Psi2Kernel N x y (x + a) = i3Psi2dK (hairerKernelTorus N) (y - x) a := by
  unfold hairerI2Psi2Kernel i3Psi2dK
  rw [show y - (x + a) = y - x - a by abel, show x - (x + a) = -a by abel]

private theorem chaos5_translate (a b : SpaceTime) :
    hairerI3Psi2Chaos5 N ρ ε ε ε ε y y' (x + a) (x + b) =
      i3Psi2Chaos5 (hairerCovariance N ρ ε) (y - x) (y' - x) a b := by
  unfold hairerI3Psi2Chaos5 i3Psi2Chaos5 hairerWickCubeSquareChaos5 i3Psi2Kernel5
  rw [show x + a - (x + b) = a - b by abel, show x + a - y' = a - (y' - x) by abel,
    show y - (x + b) = y - x - b by abel, show y - y' = y - x - (y' - x) by abel]
  rfl

private theorem chaos3_translate (a b : SpaceTime) :
    hairerI3Psi2Chaos3 N ρ ε ε ε ε y y' (x + a) (x + b) =
      i3Psi2Chaos3 (hairerCovariance N ρ ε) (y - x) (y' - x) a b := by
  unfold hairerI3Psi2Chaos3 i3Psi2Chaos3 hairerWickCubeSquareChaos3 i3Psi2Kernel3
  rw [show x + a - y = a - (y - x) by abel, show x + b - y' = b - (y' - x) by abel,
    show x + a - (x + b) = a - b by abel, show x + a - y' = a - (y' - x) by abel,
    show y - (x + b) = y - x - b by abel, show y - y' = y - x - (y' - x) by abel]
  rfl

private theorem chaos1_translate (a b : SpaceTime) :
    hairerI3Psi2Chaos1 N ρ ε ε ε ε y y' (x + a) (x + b) =
      i3Psi2Chaos1 (hairerCovariance N ρ ε) (y - x) (y' - x) a b := by
  unfold hairerI3Psi2Chaos1 i3Psi2Chaos1 hairerWickCubeSquareChaos1 i3Psi2Kernel1
  rw [show x + a - y = a - (y - x) by abel, show x + b - y' = b - (y' - x) by abel,
    show x + a - (x + b) = a - b by abel]
  rfl

private theorem cross_translate (a : SpaceTime) :
    hairerI3Psi2CrossKernel N ρ ε ε ε y y' (x + a) =
      6 * hairerCovariance N ρ ε (a - (y - x)) ^ 2 * hairerCovariance N ρ ε (a - (y' - x)) := by
  unfold hairerI3Psi2CrossKernel
  rw [show x + a - y = a - (y - x) by abel, show x + a - y' = a - (y' - x) by abel]
  rfl

/-- **The covariance of the field `hairerI3Psi2Field` is the abstract diagram `i3Psi2Cov`** at base
point `0` and the points `y - x`, `ȳ - x`. -/
theorem hairerI3Psi2Cov_eq_i3Psi2Cov :
    hairerI3Psi2Cov N ρ x ε ε y y' =
      i3Psi2Cov (hairerKernelTorus N) (hairerCovariance N ρ ε) (hairerSunsetConstant N ρ ε)
        (y - x) (y' - x) := by
  unfold hairerI3Psi2Cov i3Psi2Cov i3Psi2Double
  have d : ∀ χ : SpaceTime → SpaceTime → ℝ,
      ∀ χ' : SpaceTime → SpaceTime → ℝ,
      (∀ a b, χ (x + a) (x + b) = χ' a b) →
      ∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        χ q.1 q.2 = ∫ q : SpaceTime × SpaceTime,
          i3Psi2dK (hairerKernelTorus N) (y - x) q.1 * i3Psi2dK (hairerKernelTorus N) (y' - x) q.2 *
            χ' q.1 q.2 := by
    intro χ χ' hχ
    rw [integral_prod_translate x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [kernel_translate, hχ]
  have e5 := d _ _ (chaos5_translate N ρ ε x y y')
  have e3 := d _ _ (chaos3_translate N ρ ε x y y')
  have e1 := d _ _ (chaos1_translate N ρ ε x y y')
  have c1 : (∫ w, hairerI2Psi2Kernel N x y w * hairerI3Psi2CrossKernel N ρ ε ε ε y y' w) =
      ∫ w, i3Psi2dK (hairerKernelTorus N) (y - x) w *
        (6 * hairerCovariance N ρ ε (w - (y - x)) ^ 2 * hairerCovariance N ρ ε (w - (y' - x))) := by
    rw [integral_translate x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [kernel_translate, cross_translate]
  have c2 : (∫ w, hairerI2Psi2Kernel N x y' w * hairerI3Psi2CrossKernel N ρ ε ε ε y' y w) =
      ∫ w, i3Psi2dK (hairerKernelTorus N) (y' - x) w *
        (6 * hairerCovariance N ρ ε (w - (y' - x)) ^ 2 * hairerCovariance N ρ ε (w - (y - x))) := by
    rw [integral_translate x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [kernel_translate, cross_translate]
  rw [e5, e3, e1, c1, c2, sub_sub_sub_cancel_right]
  rfl

end RegularityStructures.Phi43

end
