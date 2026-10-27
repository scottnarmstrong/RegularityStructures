module

public import GlobalPhi43.Attachment.ProbeKernelPairing
public import GlobalPhi43.Attachment.ProbePsiAverage
public import RegularityStructures.PDE.HeatOpBridge
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Identification of the Gaussian pairing with the actual torus heat average.
The heat kernel, field, and averaging cutoff are unchanged. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE MeasureTheory Set

namespace GlobalPhi43.Attachment

def probeJPath (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) :
    C(ℝ, C(Torus3, ℝ)) := ContinuousMap.curry ⟨treeJ N f, continuous_treeJ hf⟩

def probeJAverage (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (s t : ℝ) : C(Torus3, ℝ) := probePsiAverage (probeJPath N f hf) s t

theorem probeJAverage_eq_pairing {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (y : ProbeSpace) :
    probeJAverage N f hf s (r^2) (torusProj y) =
      ∫ w, treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) ((s+r^2,y)-w) := by
  have : (volume : Measure ParabolicSpace).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  let z : ParabolicSpace := (s+r^2,y)
  have hi := probeJ_pairing_integrable (N := N) hf s hr hr1 z rfl
  have hi' := (Measure.measurePreserving_sub_left volume z).integrable_comp_of_integrable hi
  have hi'' : Integrable (fun v : ParabolicSpace =>
      treeJ N f (spaceTimeProj (z-v))*probeGaussianKernel (r^2) v) := by
    simpa only [Function.comp_def, sub_sub_cancel] using hi'
  have href : (∫ w, treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)) =
      ∫ v, treeJ N f (spaceTimeProj (z-v))*probeGaussianKernel (r^2) v := by
    have hh := integral_sub_left_eq_self
      (fun w => treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)) volume z
    simpa only [sub_sub_cancel] using hh.symm
  rw [href]
  rw [Measure.volume_eq_prod] at hi'' ⊢
  rw [integral_prod _ hi'']
  change probePsiAverage (probeJPath N f hf) s (r^2) (torusProj y) = _
  rw [probePsiAverage, ContinuousMap.integral_apply
    (probePsiAverage_integrable _ s (sq_pos_of_pos hr))]
  apply integral_congr_ae
  apply ae_of_all
  intro τ
  change probeTimeWeight (r^2) τ * heatOp τ (probeJPath N f hf (s+r^2-τ)) (torusProj y) = _
  by_cases hw : probeTimeWeight (r^2) τ = 0
  · simp only [probeGaussianKernel, hw, zero_mul, mul_zero, integral_zero]
  have ht := (probeTimeWeight_support (sq_pos_of_pos hr) (subset_closure hw)).1
  have hτ : 0 < τ := by nlinarith [sq_pos_of_pos hr]
  rw [heatOp_eq_heatSemigroup hτ, heatSemigroup, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have he : spaceTimeProj (z-(τ,v)) = (s+r^2-τ, torusProj y-torusProj v) := by
    apply Prod.ext
    · rfl
    · exact torusProj_sub y v
  dsimp only
  rw [he]
  simp only [probeGaussianKernel, heatKernelR4, hτ, ite_true]
  change probeTimeWeight (r^2) τ *
    (gaussKernel τ v * treeJ N f (s+r^2-τ, torusProj y-torusProj v)) = _
  ring

end GlobalPhi43.Attachment
