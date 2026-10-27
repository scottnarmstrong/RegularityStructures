module

public import GlobalPhi43.Attachment.ProbeJWindow
public import GlobalPhi43.Attachment.ProbeKernelIntegral
public import GlobalPhi43.Attachment.ProbePieceGeometry
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual Gaussian pairing is integrable on the source observation window.
The auxiliary field bound is produced from continuity on the time-torus compact. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set

namespace GlobalPhi43.Attachment

theorem probeGaussianKernel_reflect_integrable {r : ℝ} (hr : 0 < r) (z : ParabolicSpace) :
    Integrable (fun w => probeGaussianKernel (r^2) (z-w)) := by
  have : (volume : Measure ParabolicSpace).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  exact (Measure.measurePreserving_sub_left volume z).integrable_comp_of_integrable
    (probeGaussianKernel_integrable hr)

/-- The time restriction used only to dominate integrands is proved directly
from the actual chi_t support. -/
theorem probeGaussianKernel_window {s r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {z w : ParabolicSpace} (hz : z.1 = s+r^2)
    (hk : probeGaussianKernel (r^2) (z-w) ≠ 0) : w.1 ∈ Icc s (s+1) := by
  have ht := probeGaussianKernel_time_support (sq_pos_of_pos hr) (subset_closure hk)
  change r^2/2 ≤ z.1-w.1 ∧ z.1-w.1 ≤ 3*r^2/4 at ht
  rw [hz] at ht
  constructor <;> nlinarith [ht.1, ht.2]

/-- Constants here may depend on J solely for dominated integration; they
are not used in the model bound on the resulting integral. -/
theorem probeJ_pairing_domination {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ParabolicSpace) (hz : z.1 = s+r^2) :
    ∃ M : ℝ, 0 ≤ M ∧ Integrable (fun w => M*probeGaussianKernel (r^2) (z-w)) ∧
      ∀ w, ‖treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)‖ ≤
        M*probeGaussianKernel (r^2) (z-w) := by
  obtain ⟨M, hM, hb⟩ := probeJ_window_bound hf s
  refine ⟨M, hM, (probeGaussianKernel_reflect_integrable hr z).const_mul M, ?_⟩
  intro w
  by_cases hk : probeGaussianKernel (r^2) (z-w) = 0
  · simp only [hk, mul_zero, norm_zero, le_refl]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (probeGaussianKernel_nonneg (sq_pos_of_pos hr) _)]
  exact mul_le_mul_of_nonneg_right (hb w (probeGaussianKernel_window hr hr1 hz hk))
    (probeGaussianKernel_nonneg (sq_pos_of_pos hr) _)

theorem probeJ_pairing_integrable {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ParabolicSpace) (hz : z.1 = s+r^2) :
    Integrable (fun w => treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)) := by
  obtain ⟨M, _, hi, hb⟩ := probeJ_pairing_domination hf s hr hr1 z hz
  exact hi.mono' (((continuous_treeJ hf).comp continuous_spaceTimeProj).mul
    ((probeGaussianKernel_smooth hr).continuous.comp (by fun_prop))).aestronglyMeasurable
    (ae_of_all _ hb)

end GlobalPhi43.Attachment
