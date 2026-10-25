/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradKernel
import Mathlib.Tactic

/-!
# Majorant of the Taylor remainder kernel

For `θ ∈ [0, 1]`, a lift `a` with `|aᵢ| ≤ 1/2` and `|t| ≤ 1`, the kernel
`hairerTaylorKernel N x t a` satisfies the majorant hypothesis `gammaMajorant` with decay `4 + θ`
and gain `1 + θ` in terms of `r = ‖(t, a)‖_𝔰`, with a constant independent of `x`, `t`, `a`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gt_sub_zero {N : ℕ} {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ} {w : SpaceTime}
    (ht : |t| ≤ 1) (hs : ¬ |w.1 - x.1| ≤ 2) : hairerTaylorKernel N x t a w = 0 := by
  unfold hairerTaylorKernel
  have h1 : 1 < |(x + (t, torusProj a) - w).1| := by
    simp only [Prod.fst_sub, Prod.fst_add]
    have : |w.1 - x.1| ≤ |t| + |x.1 + t - w.1| := by
      calc |w.1 - x.1| = |t - (x.1 + t - w.1)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith [not_le.1 hs]
  have h2 : 1 < |(x - w).1| := by
    simp only [Prod.fst_sub]
    rw [abs_sub_comm]
    linarith [not_le.1 hs]
  rw [hairerKernelTorus_eq_zero_of_one_lt_time N h1, hairerKernelTorus_eq_zero_of_one_lt_time N h2]
  simp [hairerKernelTorusGrad_eq_zero_of_one_lt_time _ _ h2]

/-- **Majorant of the Taylor remainder kernel**: decay `4 + θ`, gain `1 + θ`, `θ ∈ [0, 1]`. -/
theorem gammaMajorant_hairerTaylorKernel (N : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}, (∀ i, |a i| ≤ 1 / 2) →
      |t| ≤ 1 → gammaMajorant (hairerTaylorKernel N x t a) x (x + (t, torusProj a))
        (parabolicNorm (t, a)) M (1 + θ) (4 + θ) := by
  obtain ⟨CT, hCT, hT⟩ := hairerKernelTorus_taylor_abs_le N
  obtain ⟨C1, hC1, hG⟩ := hairerKernelTorusGrad_abs_le N
  obtain ⟨B3, hB3, -, -, -, hKb, -⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  refine ⟨CT + 25 * B3 + 75 * C1, by positivity, fun {x t a} ha ht =>
    ⟨parabolicNorm_nonneg _, by positivity, measurable_hairerTaylorKernel N x t a, ?_⟩⟩
  intro w hy hx
  by_cases hs : |w.1 - x.1| ≤ 2
  · rw [i2Psi2Slab_of_le hs, one_mul]
    set r := parabolicNorm (t, a) with hr
    have hr0 : 0 ≤ r := parabolicNorm_nonneg _
    have hv : x + (t, torusProj a) - w = (x - w) + (t, torusProj a) := by abel
    have hP : 0 ≤ r ^ (1 + θ) := Real.rpow_nonneg hr0 _
    have hSv : 0 ≤ torusParabolicSize (x + (t, torusProj a) - w) ^ (-(4 + θ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have hSu : 0 ≤ torusParabolicSize (x - w) ^ (-(4 + θ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    unfold hairerTaylorKernel
    by_cases hfar : 2 * r ≤ torusParabolicSize (x - w)
    · have h1 := hT hθ0 hθ1 (t := t) hx ha (by linarith)
      rw [← hv] at h1
      refine gammaMajorant_alg_le (A := CT) (by positivity) hP hSv hSu ?_ (by linarith)
      rw [← mul_assoc]; exact h1
    · have hlt : torusParabolicSize (x - w) < 2 * r := lt_of_not_ge hfar
      have hsh : torusParabolicSize ((t, torusProj a)) ≤ r := torusParabolicSize_proj_le t a
      have hsv : torusParabolicSize (x + (t, torusProj a) - w) ≤ 5 * r := by
        have := torusParabolicSize_add_le_add (x - w) (t, torusProj a)
        rw [← hv] at this
        linarith
      have hc2 : 1 + θ ≤ 2 := by linarith
      have k1 := gammaMajorant_rpow_near hy hr0 hsv (c := 1 + θ) (m := 3) (by linarith) hc2
      have k2 := gammaMajorant_rpow_near hx hr0 (by linarith) (c := 1 + θ) (m := 3)
        (by linarith) hc2
      have g2 := gammaMajorant_rpow_near hx hr0 (by linarith) (c := θ) (m := 4) hθ0 (by linarith)
      rw [show (3 : ℝ) + (1 + θ) = 4 + θ by ring] at k1 k2
      have bK1 := (hKb _ hy).trans (mul_le_mul_of_nonneg_left k1 hB3)
      have bK2 := (hKb _ hx).trans (mul_le_mul_of_nonneg_left k2 hB3)
      have hrpos : 0 < r := by linarith [torusParabolicSize_nonneg (x - w)]
      have hai : ∀ i, |a i| ≤ r := fun i => by
        refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)).trans ?_
        simp only [hr, parabolicNorm]
        linarith [Real.sqrt_nonneg |t|]
      have gsum : |∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i| ≤
          75 * C1 * (r ^ (1 + θ) * torusParabolicSize (x - w) ^ (-(4 + θ))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hterm : ∀ i : Fin 3, |hairerKernelTorusGrad N i (x - w) * a i| ≤
            25 * C1 * (r ^ (1 + θ) * torusParabolicSize (x - w) ^ (-(4 + θ))) := fun i => by
          rw [abs_mul]
          have e : r ^ (1 + θ) = r * r ^ θ := by
            rw [Real.rpow_add hrpos, Real.rpow_one]
          calc _ ≤ (C1 * torusParabolicSize (x - w) ^ (-(4 : ℝ))) * r :=
              mul_le_mul (hG i hx) (hai i) (abs_nonneg _) (by
                exact mul_nonneg hC1 (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
            _ ≤ (C1 * (25 * r ^ θ * torusParabolicSize (x - w) ^ (-(4 + θ)))) * r :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left g2 hC1) hr0
            _ = _ := by rw [e]; ring
        calc _ ≤ ∑ _i : Fin 3, 25 * C1 * (r ^ (1 + θ) * torusParabolicSize (x - w) ^ (-(4 + θ))) :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = _ := by simp; ring
      have hab : |hairerKernelTorus N (x + (t, torusProj a) - w) - hairerKernelTorus N (x - w) -
          ∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i| ≤
          |hairerKernelTorus N (x + (t, torusProj a) - w)| + |hairerKernelTorus N (x - w)| +
          |∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i| := by
        have e1 := abs_sub (hairerKernelTorus N (x + (t, torusProj a) - w) -
          hairerKernelTorus N (x - w)) (∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i)
        have e2 := abs_sub (hairerKernelTorus N (x + (t, torusProj a) - w))
          (hairerKernelTorus N (x - w))
        linarith
      generalize torusParabolicSize (x + (t, torusProj a) - w) ^ (-(4 + θ)) = Sv at *
      generalize torusParabolicSize (x - w) ^ (-(4 + θ)) = Su at *
      generalize r ^ (1 + θ) = P at *
      nlinarith [mul_nonneg hP hSv, mul_nonneg hP hSu, mul_nonneg hCT (mul_nonneg hP hSv),
        mul_nonneg hCT (mul_nonneg hP hSu)]
  · rw [gt_sub_zero ht hs]
    have : i2Psi2Slab x.1 w = 0 := by unfold i2Psi2Slab; simp [hs]
    rw [this]
    simp

end RegularityStructures.Phi43

end
