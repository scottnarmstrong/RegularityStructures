/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelGaussianConvolution
public import RegularityStructures.Torus.HeatKernelRegularity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gaussian convolution on the torus

The periodised Gaussian is a convolution semigroup.  The proof unfolds the periodisation only
inside the Euclidean integral; the resulting Gaussian series is exchanged with the integral by
absolute summability.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures

private theorem torusRep_mem_Ico_for_convolution (x : Torus3) (i : Fin 3) :
    torusRep x i ∈ Ico (0 : ℝ) 1 := by
  change (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ) ∈ Ico 0 1
  simpa using (AddCircle.equivIco (1 : ℝ) 0 (x i)).property

private theorem gaussKernel_norm_le_prefactor {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    ‖gaussKernel t y‖ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) := by
  rw [Real.norm_of_nonneg (gaussKernel_nonneg ht y)]
  unfold gaussKernel
  have hfac : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) := by positivity
  have hexp : exp (-sqNorm3 y / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hden : 0 ≤ 4 * t := by positivity
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Finset.sum_nonneg fun i _ => sq_nonneg (y i))) hden
  simpa using mul_le_mul_of_nonneg_left hexp hfac

theorem integral_heatKernel_mul_heatKernel_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : Torus3) :
    ∫ y : Fin 3 → ℝ, gaussKernel s y * heatKernel t (x - torusProj y) =
      heatKernel (s + t) x := by
  let a : Fin 3 → ℝ := torusRep x
  have torusProj_sub_local (u v : Fin 3 → ℝ) :
      torusProj (u - v) = torusProj u - torusProj v := by
    funext i
    simp [torusProj]
  have hrep : torusProj (torusRep x) = x := by
    funext i
    simp [torusProj, torusRep]
  have harg : ∀ y : Fin 3 → ℝ,
      heatKernel t (x - torusProj y) = heatKernelLift t (a - y) := by
    intro y
    have hproj : torusProj (a - y) = x - torusProj y := by
      dsimp [a]
      rw [torusProj_sub_local, hrep]
    rw [← hproj, heatKernel_comp_torusProj_eq_lift]
  have hst : 0 < s + t := by linarith
  let F : (Fin 3 → ℤ) → (Fin 3 → ℝ) → ℝ := fun k y =>
    gaussKernel s y * gaussKernel t ((a + (fun i => (k i : ℝ))) - y)
  have hFint : ∀ k : Fin 3 → ℤ, Integrable (F k) := by
    intro k
    have hcont : Continuous (fun y : Fin 3 → ℝ =>
        gaussKernel t ((a + (fun i => (k i : ℝ))) - y)) := by
      exact (continuous_gaussKernel_fixed ht).comp
        ((continuous_const.add continuous_const).sub continuous_id)
    exact (integrable_gaussKernel hs).mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => gaussKernel_norm_le_prefactor ht _)
  have hFnonneg : ∀ k y, 0 ≤ F k y := by
    intro k y
    dsimp [F]
    exact mul_nonneg (gaussKernel_nonneg hs _) (gaussKernel_nonneg ht _)
  have hFint_norm : ∀ k : Fin 3 → ℤ, Integrable (fun y => ‖F k y‖) := by
    intro k
    exact (hFint k).norm
  have hFsum : Summable (fun k : Fin 3 → ℤ => ∫ y, ‖F k y‖) := by
    have hEq : ∀ k : Fin 3 → ℤ, ∫ y, ‖F k y‖ =
        gaussKernel (s + t) (a + fun i => (k i : ℝ)) := by
      intro k
      have hnorm : (fun y => ‖F k y‖) = F k := by
        funext y
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg k y)]
      rw [hnorm]
      calc
        ∫ y, F k y = ∫ y, gaussKernel s y *
            gaussKernel t ((a + (fun i => (k i : ℝ))) - y) := by rfl
        _ = gaussKernel (s + t) (a + fun i => (k i : ℝ)) :=
          integral_gaussKernel_mul_gaussKernel_sub hs ht _
      
    rw [show (fun k : Fin 3 → ℤ => ∫ y, ‖F k y‖) =
        (fun k : Fin 3 → ℤ => gaussKernel (s + t) (a + fun i => (k i : ℝ))) by
          funext k; exact hEq k]
    exact summable_gaussKernel_shift hst a (fun i => torusRep_mem_Ico_for_convolution x i)
  have hswap : (∫ y : Fin 3 → ℝ, ∑' k : Fin 3 → ℤ, F k y) =
      ∑' k : Fin 3 → ℤ, ∫ y : Fin 3 → ℝ, F k y := by
    exact (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  calc
    ∫ y : Fin 3 → ℝ, gaussKernel s y * heatKernel t (x - torusProj y) =
        ∫ y : Fin 3 → ℝ, gaussKernel s y * heatKernelLift t (a - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [harg y]
    _ = ∫ y : Fin 3 → ℝ, ∑' k : Fin 3 → ℤ, F k y := by
          apply integral_congr_ae
          filter_upwards [] with y
          unfold F heatKernelLift
          rw [← tsum_mul_left]
          apply tsum_congr
          intro k
          congr 2
          funext i
          simp only [Pi.add_apply, Pi.sub_apply]
          ring
    _ = ∑' k : Fin 3 → ℤ, ∫ y : Fin 3 → ℝ, F k y := hswap
    _ = ∑' k : Fin 3 → ℤ,
        gaussKernel (s + t) (a + fun i => (k i : ℝ)) := by
          apply tsum_congr
          intro k
          simpa [F] using integral_gaussKernel_mul_gaussKernel_sub hs ht
            (a + fun i => (k i : ℝ))
    _ = heatKernel (s + t) x := by
          unfold heatKernel
          rfl

theorem heatSemigroup_heatKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : Torus3) :
    heatSemigroup s ⟨heatKernel t, continuous_heatKernel_fixed ht⟩ x =
      heatKernel (s + t) x := by
  unfold heatSemigroup
  exact integral_heatKernel_mul_heatKernel_sub hs ht x

end RegularityStructures

end
