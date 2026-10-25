/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoCov
public import Phi43.BPHZ.TreeI3Psi2DifferenceKernels
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneIdentity

/-!
# The covariance of the difference as an abstract diagram

`hairerI3Psi2CovTwo N ρ ρ' x a b y y'` equals the abstract diagram `i3Psi2CovPair` at base point `0`
and the points `y - x`, `y' - x`, with `K = hairerKernelTorus N` and the covariances
`Q_aa, Q_ab, Q_ba, Q_bb` of `(ρ, a)`, `(ρ', b)`.  The second difference of the four covariances is
the sum of the chaos-`5` and chaos-`3` double integrals of the second differences of the kernels
(`i3Psi2DiffChi5`, `i3Psi2DiffChi3`) and of the chaos-`1` term `36 ∫ (D^a_z - D^b_z)(D^a_{z'} - D^b_{z'})`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The chaos-`3` kernel with entries `Q_aa(w - z)`, `Q_bb(v - z')` and the cross covariance
`Q_ab` elsewhere. -/
def i3Psi2Chaos3Gen (Qaa Qbb Qab : SpaceTime → ℝ) (z z' w v : SpaceTime) : ℝ :=
  i3Psi2Kernel3 (Qaa (w - z)) (Qbb (v - z')) (Qab (w - v)) (Qab (w - z')) (Qab (z - v))
    (Qab (z - z'))

/-- The abstract covariance `E[F_a(z) F_b(z')]` of the fields of `I(Ψ³)Ψ²` for two kernels. -/
def i3Psi2CovPair (K Qaa Qab Qba Qbb : SpaceTime → ℝ) (ca cb : ℝ) (z z' : SpaceTime) : ℝ :=
  i3Psi2Double K (i3Psi2Chaos5 Qab) z z' + i3Psi2Double K (i3Psi2Chaos3Gen Qaa Qbb Qab) z z' +
    i3Psi2Chaos1TotalPair K Qaa Qab Qba Qbb ca cb z z'

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ) (x y y' : SpaceTime)

private theorem integral_prod_translate' (F : SpaceTime × SpaceTime → ℝ) :
    ∫ q : SpaceTime × SpaceTime, F q = ∫ q : SpaceTime × SpaceTime, F (x + q.1, x + q.2) := by
  have hmp : MeasurePreserving (fun q : SpaceTime × SpaceTime => (x + q.1, x + q.2))
      ((volume : Measure SpaceTime).prod volume) ((volume : Measure SpaceTime).prod volume) :=
    (measurePreserving_add_left volume x).prod (measurePreserving_add_left volume x)
  exact (hmp.integral_comp (MeasurableEquiv.prodCongr (MeasurableEquiv.addLeft x)
    (MeasurableEquiv.addLeft x)).measurableEmbedding F).symm

private theorem integral_translate' (F : SpaceTime → ℝ) :
    ∫ w : SpaceTime, F w = ∫ a : SpaceTime, F (x + a) :=
  (integral_add_left_eq_self F x).symm

private theorem kernel_translate' (a : SpaceTime) :
    hairerI2Psi2Kernel N x y (x + a) = i3Psi2dK (hairerKernelTorus N) (y - x) a := by
  unfold hairerI2Psi2Kernel i3Psi2dK
  rw [show y - (x + a) = y - x - a by abel, show x - (x + a) = -a by abel]

/-- **The covariance at two mollifiers is the abstract diagram** `i3Psi2CovPair`. -/
theorem hairerI3Psi2CovTwo_eq_i3Psi2CovPair :
    hairerI3Psi2CovTwo N ρ ρ' x a b y y' =
      i3Psi2CovPair (hairerKernelTorus N) (hairerCrossCovarianceTwo N ρ a ρ a)
        (hairerCrossCovarianceTwo N ρ a ρ' b) (hairerCrossCovarianceTwo N ρ' b ρ a)
        (hairerCrossCovarianceTwo N ρ' b ρ' b) (hairerSunsetConstant N ρ a)
        (hairerSunsetConstant N ρ' b) (y - x) (y' - x) := by
  have d : ∀ χ : SpaceTime → SpaceTime → ℝ, ∀ χ' : SpaceTime → SpaceTime → ℝ,
      (∀ a b, χ (x + a) (x + b) = χ' a b) →
      ∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        χ q.1 q.2 = ∫ q : SpaceTime × SpaceTime,
          i3Psi2dK (hairerKernelTorus N) (y - x) q.1 * i3Psi2dK (hairerKernelTorus N) (y' - x) q.2 *
            χ' q.1 q.2 := by
    intro χ χ' hχ
    rw [integral_prod_translate' x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [kernel_translate', hχ]
  have e5 := d (hairerI3Psi2Chaos5Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y')
    (i3Psi2Chaos5 (hairerCrossCovarianceTwo N ρ a ρ' b) (y - x) (y' - x)) (by
      intro u v
      unfold hairerI3Psi2Chaos5Two i3Psi2Chaos5 hairerWickCubeSquareChaos5 i3Psi2Kernel5
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rw [show x + u - (x + v) = u - v by abel, show x + u - y' = u - (y' - x) by abel,
        show y - (x + v) = y - x - v by abel, show y - y' = y - x - (y' - x) by abel])
  have e3 := d (hairerI3Psi2Chaos3Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y')
    (i3Psi2Chaos3Gen (hairerCrossCovarianceTwo N ρ a ρ a) (hairerCrossCovarianceTwo N ρ' b ρ' b)
      (hairerCrossCovarianceTwo N ρ a ρ' b) (y - x) (y' - x)) (by
      intro u v
      unfold hairerI3Psi2Chaos3Two i3Psi2Chaos3Gen hairerWickCubeSquareChaos3 i3Psi2Kernel3
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rw [show x + u - y = u - (y - x) by abel, show x + v - y' = v - (y' - x) by abel,
        show x + u - (x + v) = u - v by abel, show x + u - y' = u - (y' - x) by abel,
        show y - (x + v) = y - x - v by abel, show y - y' = y - x - (y' - x) by abel])
  have e1 := d (hairerI3Psi2Chaos1Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y')
    (i3Psi2Chaos1Gen (hairerCrossCovarianceTwo N ρ a ρ a) (hairerCrossCovarianceTwo N ρ' b ρ' b)
      (hairerCrossCovarianceTwo N ρ a ρ' b) (y - x) (y' - x)) (by
      intro u v
      unfold hairerI3Psi2Chaos1Two i3Psi2Chaos1Gen hairerWickCubeSquareChaos1 i3Psi2Kernel1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rw [show x + u - y = u - (y - x) by abel, show x + v - y' = v - (y' - x) by abel,
        show x + u - (x + v) = u - v by abel])
  have c1 : (∫ w, hairerI2Psi2Kernel N x y w *
      hairerI3Psi2CrossKernelTwo N ![ρ, ρ, ρ'] ![a, a, b] y y' w) =
      ∫ w, i3Psi2dK (hairerKernelTorus N) (y - x) w *
        (6 * hairerCrossCovarianceTwo N ρ a ρ a (w - (y - x)) ^ 2 *
          hairerCrossCovarianceTwo N ρ a ρ' b (w - (y' - x))) := by
    rw [integral_translate' x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [kernel_translate']
    unfold hairerI3Psi2CrossKernelTwo
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [show x + u - y = u - (y - x) by abel, show x + u - y' = u - (y' - x) by abel]
  have c2 : (∫ w, hairerI2Psi2Kernel N x y' w *
      hairerI3Psi2CrossKernelTwo N ![ρ', ρ', ρ] ![b, b, a] y' y w) =
      ∫ w, i3Psi2dK (hairerKernelTorus N) (y' - x) w *
        (6 * hairerCrossCovarianceTwo N ρ' b ρ' b (w - (y' - x)) ^ 2 *
          hairerCrossCovarianceTwo N ρ' b ρ a (w - (y - x))) := by
    rw [integral_translate' x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [kernel_translate']
    unfold hairerI3Psi2CrossKernelTwo
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [show x + u - y = u - (y - x) by abel, show x + u - y' = u - (y' - x) by abel]
  unfold hairerI3Psi2CovTwo i3Psi2CovPair i3Psi2Chaos1TotalPair
  rw [e5, e3, e1, c1, c2]
  unfold i3Psi2Double
  rw [show y - y' = y - x - (y' - x) by abel]
  ring

end RegularityStructures.Phi43

end
