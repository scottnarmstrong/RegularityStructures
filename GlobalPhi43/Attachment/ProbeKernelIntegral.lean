module

public import GlobalPhi43.Attachment.ProbeKernelNormalization
public import Mathlib.MeasureTheory.Integral.Prod

/-! Integrability and mass of the actual compact-time Gaussian probe. -/

@[expose] public noncomputable section

open RegularityStructures MeasureTheory Set

namespace GlobalPhi43.Attachment

theorem probeGaussianKernel_nonneg {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    0 ≤ probeGaussianKernel t z :=
  mul_nonneg (probeTimeWeight_nonneg ht _) (heatKernelR4_nonneg _)

theorem probeGaussianKernel_time_support {t : ℝ} (ht : 0 < t) :
    tsupport (probeGaussianKernel t) ⊆ {z | z.1 ∈ Icc (t/2) (3*t/4)} := by
  apply closure_minimal _ (isClosed_Icc.preimage continuous_fst)
  intro z hz
  have he : probeTimeWeight t z.1 ≠ 0 := by
    intro hh
    exact hz (by simp only [probeGaussianKernel, hh, zero_mul])
  exact probeTimeWeight_support ht (subset_closure he)

theorem probeGaussianKernel_slice_integrable (t τ : ℝ) :
    Integrable (fun y : ProbeSpace => probeGaussianKernel t (τ,y)) := by
  by_cases hτ : 0 < τ
  · change Integrable (fun y => probeTimeWeight t τ * heatKernelR4 (τ,y))
    simp only [heatKernelR4, hτ, ite_true]
    exact (integrable_gaussKernel hτ).const_mul _
  · have he : (fun y : ProbeSpace => probeGaussianKernel t (τ,y)) = 0 := by
      funext y
      simp only [probeGaussianKernel, heatKernelR4, hτ, ite_false, mul_zero, Pi.zero_apply]
    rw [he]
    exact integrable_zero _ _ _

theorem probeGaussianKernel_slice_mass {t : ℝ} (ht : 0 < t) (τ : ℝ) :
    (∫ y : ProbeSpace, probeGaussianKernel t (τ,y)) = probeTimeWeight t τ := by
  by_cases hτ : 0 < τ
  · change (∫ y : ProbeSpace, probeTimeWeight t τ * heatKernelR4 (τ,y)) = _
    rw [integral_const_mul, integral_heatKernelR4_slice hτ, mul_one]
  · have hw : probeTimeWeight t τ = 0 := by
      by_contra hn
      have hh := (probeTimeWeight_support ht (subset_closure hn)).1
      linarith
    simp only [probeGaussianKernel, hw, zero_mul, integral_zero]

theorem probeGaussianKernel_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (probeGaussianKernel (r^2)) := by
  have ht : 0 < r^2 := sq_pos_of_pos hr
  rw [Measure.volume_eq_prod]
  apply (integrable_prod_iff (probeGaussianKernel_smooth hr).continuous.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (probeGaussianKernel_slice_integrable _), ?_⟩
  have he : (fun τ => ∫ y : ProbeSpace, ‖probeGaussianKernel (r^2) (τ,y)‖) =
      probeTimeWeight (r^2) := by
    funext τ
    simp only [Real.norm_of_nonneg (probeGaussianKernel_nonneg ht _)]
    exact probeGaussianKernel_slice_mass ht τ
  rw [he]
  exact (probeTimeWeight_smooth _).continuous.integrable_of_hasCompactSupport
    (probeTimeWeight_compact ht)
end GlobalPhi43.Attachment
