module

public import GlobalPhi43.Attachment.ReferenceKernelPlateau

/-! The plateau has enough volume to normalize without exceeding one. -/

public noncomputable section
namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures Set

/-- Literal plateau box volume: (3/4)*(3/2)^3=81/32. -/
theorem referenceKernelInner_volume : volume referenceKernelInner = ENNReal.ofReal (81/32 : ℝ) := by
  unfold referenceKernelInner
  rw [Measure.volume_eq_prod, Set.Icc_prod_eq]
  rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc_pi]
  norm_num [Fin.prod_univ_succ]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3/2), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem referenceKernelPlateau_mass_ge_one : 1 ≤ ∫ z, referenceKernelPlateau z := by
  have hK : MeasurableSet referenceKernelInner := measurableSet_Icc
  have hfin : volume referenceKernelInner ≠ ⊤ := by rw [referenceKernelInner_volume]; exact ENNReal.ofReal_ne_top
  have hi : Integrable (referenceKernelInner.indicator (fun _ : ParabolicSpace => (1 : ℝ))) :=
    (integrable_indicator_iff hK).2 (integrableOn_const (C := (1 : ℝ)) hfin)
  have hh : (∫ z, referenceKernelInner.indicator (fun _ : ParabolicSpace => (1 : ℝ)) z) ≤
      ∫ z, referenceKernelPlateau z := by
    apply integral_mono hi referenceKernelPlateau_integrable
    intro z
    by_cases hz : z ∈ referenceKernelInner
    · rw [Set.indicator_of_mem hz, referenceKernelPlateau_one hz]
    · rw [Set.indicator_of_notMem hz]
      exact referenceKernelPlateau_nonneg z
  rw [integral_indicator hK, integral_const, smul_eq_mul, mul_one] at hh
  simp only [Measure.real, Measure.restrict_apply_univ, referenceKernelInner_volume] at hh
  norm_num at hh
  linarith

end GlobalPhi43.Attachment
