module

public import GlobalPhi43.Attachment.NoiseSliceBound
public import GlobalPhi43.Attachment.SourceMajorantComparison

/-! # Source M-to-Q comparison: the analytic slice premise is discharged -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- The noiseSlice bound on the radius-four enlargement, using its
inclusion in the domain I. -/
theorem majorant_slice_row (κ : Kappa) :
    ∃ H : ℝ≥0, ∀ (a : Flow.LiftData 5 κ) (s : ℝ), 0 ≤ s → ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
        (smoothNoiseJ 5 ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)) ≤
      (H : ℝ≥0∞) * (Flow.unitPotentialSize (Flow.lossExponent κ) s a.potential +
        (1+a.model.normOn (gamma κ) (Flow.majorantRegion s))^3) := by
  obtain ⟨H, hH, h⟩ := noiseSlice_bound 5 κ
  refine ⟨NNReal.mk H hH.le, ?_⟩
  intro a s _ t ht
  have hb := h (fun _ : Unit => a.forcing)
    (fun _ => Flow.smooth_of_moderateLift a.moderate) () a.constants a.model
    a.moderate.1 a.moderate.2.1 a.potential a.moderate.2.2 s
  have hn := attachment_normOn_mono a.model (sliceRadiusFour_subset_majorant s)
  have hw : ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
      (smoothNoiseJ 5 ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)) ≤
      noiseSlice 5 (Flow.lossExponent κ) s (fun _ : Unit => a.forcing)
        (fun _ => Flow.smooth_of_moderateLift a.moderate) () := by
    rw [noiseSlice_eq]
    exact le_iSup_of_le (⟨t, ht⟩ : Ioc (0 : ℝ) 1) le_rfl
  rw [ENNReal.ofReal_eq_coe_nnreal hH.le] at hb
  exact (hw.trans hb).trans (mul_le_mul_right (add_le_add le_rfl
    (pow_le_pow_left' (add_le_add le_rfl hn) 3)) _)

end GlobalPhi43.Attachment
