module

public import GlobalPhi43.MW20.SourceCubicCommutatorNorm
public import GlobalPhi43.MW20.CubicRootScale
public import GlobalPhi43.MW20.BoundedSourceFields
public import GlobalPhi43.MW20.FourForcingMaximum

/-!
# The cubic commutator contribution in MW20 (4.31)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Taking the cube root of the actual commutator supremum yields exactly
the source's T^(α/3), amplitude^(2/3), Hölder^(1/3) powers. -/
theorem source_cubic_commutator_root (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T S α : ℝ} (hT : 0 < T) (hTS : T < S) (hS : S ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    sourceSup (fun x =>
      (∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
        ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT) S ^ (1 / 3 : ℝ) ≤
      2 * cubicCommutatorScale (sourceSup v (S - T))
        (sourceHolder v α (S - T) (2 * T)) T α := by
  let D := fun x =>
    (∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
      ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT
  have hT1 : T ≤ 1 := by linarith
  have hL : 2 * T ≤ 1 := by linarith
  have hb1 := sourceSup_bddAbove_pastSmooth Φ hΦ v hv.continuous hT hT1 hTS.le
  have hb3 := sourceSup_bddAbove_pastSmooth Φ hΦ (fun z => v z ^ 3)
    (hv.continuous.pow 3) hT hT1 hTS.le
  have hbD := sourceSup_bddAbove_sub (sourceSup_bddAbove_pow hb1 3) hb3
  have hD : 0 ≤ sourceSup D S :=
    sourceSup_nonneg_of_bddAbove D ⟨hT.le.trans hTS.le, hS⟩ hbD
  have hM : 0 ≤ sourceSup v (S - T) :=
    sourceSup_nonneg_of_bddAbove v ⟨by linarith, by linarith⟩
      (sourceSup_bddAbove_of_continuousOn hv.continuous (by linarith))
  have hH := sourceHolder_nonneg
    (sourceHolder_bddAbove_of_regularity hv (sub_pos.mpr hTS) hα1 hL)
  exact cubic_commutator_root_bound hD hM hH hT.le
    (mw20_row_4_30 Φ hΦ hv hT hTS hS hα0 hα1)

end GlobalPhi43.MW20
