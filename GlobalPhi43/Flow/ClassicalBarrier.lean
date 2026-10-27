module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! The integrating-factor barrier used for classical stability. -/

public noncomputable section

open MeasureTheory Set

namespace GlobalPhi43.Flow

/-- A barrier with independent initial error and time-dependent forcing error. -/
@[expose] def classicalBarrier (k d : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (k * t) * (d + ∫ q in (0 : ℝ)..t, Real.exp (-k * q) * F q)

theorem classicalBarrier_zero (k d : ℝ) (F : ℝ → ℝ) :
    classicalBarrier k d F 0 = d := by
  simp only [classicalBarrier, mul_zero, Real.exp_zero, intervalIntegral.integral_same,
    add_zero, one_mul]

theorem classicalBarrier_hasDerivAt (k d : ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    (t : ℝ) : HasDerivAt (classicalBarrier k d F)
      (k * classicalBarrier k d F t + F t) t := by
  have hc : Continuous (fun q => Real.exp (-k * q) * F q) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hi := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : HasDerivAt (fun q : ℝ => Real.exp (k * q))
      (k * Real.exp (k * t)) t := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul k).exp
  have hprod : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
    rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
  convert he.mul (hi.const_add d) using 1
  · rfl
  · dsimp [classicalBarrier]
    calc
      k * (Real.exp (k * t) * (d + ∫ q in (0 : ℝ)..t, Real.exp (-k * q) * F q)) + F t =
        k * Real.exp (k * t) * (d + ∫ q in (0 : ℝ)..t, Real.exp (-k * q) * F q) +
          (Real.exp (k * t) * Real.exp (-k * t)) * F t := by rw [hprod]; ring
      _ = _ := by ring

theorem classicalBarrier_nonneg {k d : ℝ} {F : ℝ → ℝ} (hd : 0 ≤ d)
    (hF : ∀ q, 0 ≤ F q) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ classicalBarrier k d F t := by
  exact mul_nonneg (Real.exp_nonneg _) (add_nonneg hd
    (intervalIntegral.integral_nonneg ht (fun q _ => mul_nonneg (Real.exp_nonneg _) (hF q))))

theorem classicalBarrier_le_integral {k d : ℝ} (hk : 0 ≤ k) {F : ℝ → ℝ}
    (hF : Continuous F) (hFn : ∀ q, 0 ≤ F q) {t : ℝ} (ht : 0 ≤ t) :
    classicalBarrier k d F t ≤ Real.exp (k * t) * (d + ∫ q in (0 : ℝ)..t, F q) := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  refine add_le_add le_rfl ?_
  apply intervalIntegral.integral_mono_on ht
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF).intervalIntegrable _ _
  · exact hF.intervalIntegrable _ _
  · intro q hq
    have he : Real.exp (-k * q) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) hq.1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (hFn q)

end GlobalPhi43.Flow
