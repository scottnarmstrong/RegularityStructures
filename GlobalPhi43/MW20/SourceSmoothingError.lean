module

public import GlobalPhi43.MW20.SourceHolderBound
public import GlobalPhi43.MW20.BoundedSourceFields
public import GlobalPhi43.MW20.FiniteSmoothing

/-!
# The positive Hölder smoothing error used in MW20 (4.29)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- The actual kernel smoothing error is controlled by the actual source
Hölder seminorm on the literal larger testing cylinder. -/
theorem source_smoothing_error (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R α : ℝ} (hT : 0 < T) (hTR : T < R) (hR : R ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x - v x| ≤
      sourceHolder v α (R - T) (2 * T) * T ^ α := by
  have hT1 : T ≤ 1 := by linarith
  have hL : 2 * T ≤ 1 := by linarith
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have hb := sourceHolder_bddAbove_of_regularity hv (sub_pos.mpr hTR) hα1 hL
  have hgeom := infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR.le hx
  have hsample : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, x + y ∈ sourceClosedCylinder := by
    filter_upwards [hgeom] with y hy
    exact sourceCylinder_subset_closed (sub_nonneg.mpr hTR.le) hy
  have hi := integrable_comp_of_ae_mem_compact (infiniteKernelMeasure Φ hΦ T hT)
    v isCompact_Icc hv.continuous (fun y => x + y) (continuous_const.add continuous_id) hsample
  have hosc : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT,
      ‖v (x + y) - v x‖ ≤ sourceHolder v α (R - T) (2 * T) * T ^ α := by
    filter_upwards [hgeom, infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT1] with y hy hys
    have hd : Local.pdist x (x + y) ≤ T := by
      simpa only [Local.pdist_add_right] using hys.2
    rw [Real.norm_eq_abs]
    apply (sourceHolder_increment hb
      (sourceCylinder_antitone (sub_nonneg.mpr hTR.le) (by linarith) hx) hy
        (by linarith) hL).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x _) hd hα0) (sourceHolder_nonneg hb)
  have he : (∫ y, v (x + y) - v x ∂infiniteKernelMeasure Φ hΦ T hT) =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x - v x := by
    rw [integral_sub hi (integrable_const _)]
    simp [pastSmooth]
  have h := norm_integral_le_of_norm_le_const hosc
  rw [he] at h
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- The source norm before smoothing is bounded by the actual smoothed norm
plus the actual Hölder smoothing error, as used in (4.29). -/
theorem sourceSup_le_smoothed_add_error (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R α : ℝ} (hT : 0 < T) (hTR : T < R) (hR : R ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    sourceSup v R ≤ sourceSup (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v) R +
      sourceHolder v α (R - T) (2 * T) * T ^ α := by
  have hb := sourceSup_bddAbove_pastSmooth Φ hΦ v hv.continuous hT (by linarith) hTR.le
  apply csSup_le ((sourceCylinder_nonempty ⟨hT.le.trans hTR.le, hR⟩).image _)
  rintro b ⟨x, hx, rfl⟩
  have he := source_smoothing_error Φ hΦ hv hT hTR hR hα0 hα1 hx
  have hs : |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x| ≤
      sourceSup (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v) R := le_csSup hb ⟨x, hx, rfl⟩
  have ht := abs_sub (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x)
    (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x - v x)
  have hid : pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x -
      (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v x - v x) = v x := by ring
  rw [hid] at ht
  linarith

end GlobalPhi43.MW20
