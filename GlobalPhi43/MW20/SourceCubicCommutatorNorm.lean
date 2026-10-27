module

public import GlobalPhi43.MW20.SourceHolderBound
public import GlobalPhi43.MW20.SourceCubicSmoothing

/-!
# MW20 (4.30) with actual cylinder suprema and Hölder seminorms
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- The pointwise cubic commutator bound with the actual radius-local
Hölder seminorm. Finiteness and measurability follow from local C² regularity. -/
theorem source_cubic_commutator_holder (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R α : ℝ} (hT : 0 < T) (hT1 : 2 * T ≤ 1) (hTR : T < R)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x : ParabolicSpace}
    (hx : x ∈ sourceCylinder R) :
    |(∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
      ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT| ≤
      6 * (sourceSup v (R - T)) ^ 2 * sourceHolder v α (R - T) (2 * T) * T ^ α := by
  have hb := sourceHolder_bddAbove_of_regularity hv (sub_pos.mpr hTR) hα1 hT1
  apply source_cubic_commutator Φ hΦ hv.continuous hT (by linarith) hTR.le
    hα0 (sourceHolder_nonneg hb) hx
  intro z hz hdist
  apply sourceHolder_increment hb
    (sourceCylinder_antitone (sub_nonneg.mpr hTR.le) (by linarith) hx) hz _ hT1
  linarith

/-- MW20 (4.30), as a supremum over its literal source cylinder, with the
printed universal factor 6 and no assumed commutator or norm attachment. -/
theorem mw20_row_4_30 (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R α : ℝ} (hT : 0 < T) (hTR : T < R)
    (hR1 : R ≤ 1 / 2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    sourceSup (fun x =>
      (∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
        ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT) R ≤
      6 * (sourceSup v (R - T)) ^ 2 * sourceHolder v α (R - T) (2 * T) * T ^ α := by
  apply csSup_le ((sourceCylinder_nonempty ⟨hT.le.trans hTR.le, hR1⟩).image _)
  rintro b ⟨x, hx, rfl⟩
  exact source_cubic_commutator_holder Φ hΦ hv hT (by linarith) hTR hα0 hα1 hx

end GlobalPhi43.MW20
