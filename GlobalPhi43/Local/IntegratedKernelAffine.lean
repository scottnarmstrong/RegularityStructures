/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.KernelWeightedIntegrability
public import GlobalPhi43.Local.PastAffineError
public import GlobalPhi43.Local.SpatialLinearRepresentation

/-! Integrate the actual kernel Taylor error, obtaining the actual affine
infimum with an L1 source allowance and no derivatives of the source. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory
open scoped ContDiff ENNReal

 theorem exists_integrated_kernel_affine_bound {k : ParabolicSpace → ℝ}
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) :
    ∃ S ≥ 0, ∀ (μ : Measure ParabolicSpace) (g : ParabolicSpace → ℝ), Integrable g μ →
      ∀ (x : ParabolicSpace) (R : ℝ), 0 ≤ R →
      pastAffineError (fun p => ∫ q, k (p - q) * g q ∂μ) x R ≤
        ENNReal.ofReal (2 * S * (∫ q, |g q| ∂μ) * R ^ 2) := by
  obtain ⟨S, hS, hTaylor⟩ := exists_compact_kernel_taylor_bound hk hck
  refine ⟨S, hS, ?_⟩
  intro μ g hg x R hR
  have hi (p : ParabolicSpace) := kernel_weighted_integrable hk hck hg p
  have hid (v : ParabolicSpace) := kernel_gradient_weighted_integrable hk hck hg x v
  let c : ℝ := ∫ q, k (x - q) * g q ∂μ
  let ν : Fin 3 → ℝ := fun i => ∫ q, fderiv ℝ k (x - q) (0, Pi.single i 1) * g q ∂μ
  have hlin (y : ParabolicSpace) :
      (∫ q, fderiv ℝ k (x - q) (0, y.2 - x.2) * g q ∂μ) = spatialLinear ν (y - x) := by
    change (∫ q, fderiv ℝ k (x - q) (0, y.2 - x.2) * g q ∂μ) =
      ∑ i : Fin 3, (∫ q, fderiv ℝ k (x - q) (0, Pi.single i 1) * g q ∂μ) * (y.2 i - x.2 i)
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ (fun i _ => (hid (0, Pi.single i 1)).mul_const (y.2 i - x.2 i))]
    apply integral_congr_ae
    apply ae_of_all
    intro q
    dsimp only
    have hcoord := spatial_differential_coordinates ((fderiv ℝ k (x - q)).comp heatSpatialInsert) (y.2 - x.2)
    simp only [ContinuousLinearMap.comp_apply, heatSpatialInsert, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply] at hcoord
    rw [hcoord, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  apply iInf_le_of_le c
  apply iInf_le_of_le ν
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply ENNReal.ofReal_le_ofReal
  have heq : (∫ q, (k (y - q) - k (x - q) - fderiv ℝ k (x - q) (0, y.2 - x.2)) * g q ∂μ) =
      (∫ q, k (y - q) * g q ∂μ) - c - spatialLinear ν (y - x) := by
    simp_rw [sub_mul]
    have hdiff : Integrable (fun q => k (y - q) * g q - k (x - q) * g q) μ := by
      have hd := (hi y).sub (hi x)
      have he : ((fun q => k (y - q) * g q) - fun q => k (x - q) * g q) =
          (fun q => k (y - q) * g q - k (x - q) * g q) := by
        funext q
        rw [Pi.sub_apply]
      rw [he] at hd
      exact hd
    rw [integral_sub hdiff (hid (0, y.2 - x.2)), integral_sub (hi y) (hi x), hlin]
  have hpoint (q : ParabolicSpace) :
      ‖(k (y - q) - k (x - q) - fderiv ℝ k (x - q) (0, y.2 - x.2)) * g q‖ ≤
        (2 * S * R ^ 2) * ‖g q‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (translated_kernel_taylor hk hTaylor x y q hR hy) (norm_nonneg _)
  have hn := norm_integral_le_of_norm_le (μ := μ) (hg.norm.const_mul (2 * S * R ^ 2))
    (ae_of_all _ hpoint)
  calc
    |(∫ q, k (y - q) * g q ∂μ) - spatialAffine x c ν y| =
        ‖∫ q, (k (y - q) - k (x - q) - fderiv ℝ k (x - q) (0, y.2 - x.2)) * g q ∂μ‖ := by
      rw [heq, Real.norm_eq_abs]
      unfold spatialAffine
      congr 1
      ring
    _ ≤ ∫ q, (2 * S * R ^ 2) * ‖g q‖ ∂μ := hn
    _ = 2 * S * (∫ q, |g q| ∂μ) * R ^ 2 := by
      rw [integral_const_mul]
      simp only [Real.norm_eq_abs]
      ring

end GlobalPhi43.Local
