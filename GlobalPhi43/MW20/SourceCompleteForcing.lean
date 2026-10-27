module

public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.MW20.ReconstructionKernelTests
public import GlobalPhi43.MW20.SourceKernelTreeTests

/-! Complete renormalised forcing: recentering keeps both counterterms. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Recentring the complete B forcing preserves both C₂v and C₂J. -/
theorem source_complete_forcing_recenter
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ) (hv : Continuous v) (hV : Continuous V)
    (C₂ : ℝ) (x : ParabolicSpace) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    pastSmooth μ (fun y => v y * V y) x + 3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x) =
      (pastSmooth μ (fun y => (v y - v x) * V y) x +
        3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)) + v x * pastSmooth μ V x := by
  have hi := reconstruction_kernel_section_integrable Φ hΦ hT hT1
    (fun y => v y * V y) (hv.mul hV) x
  have hj := reconstruction_kernel_section_integrable Φ hΦ hT hT1 V hV x
  have he : pastSmooth (infiniteKernelMeasure Φ hΦ T hT)
      (fun y => (v y - v x) * V y) x =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y * V y) x -
        v x * pastSmooth (infiniteKernelMeasure Φ hΦ T hT) V x := by
    unfold pastSmooth
    simp_rw [sub_mul]
    rw [integral_sub hi (hj.const_mul (v x)), integral_const_mul]
  dsimp only
  rw [he]
  ring

/-- Actual ordinary negative tree budgets bound their smoothed field at
any centre of the parent cylinder. This includes V and W in (4.31). -/
theorem source_negative_forcing_test
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : ParabolicSpace → ℝ) {r a c M p T : ℝ}
    (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hbudget : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) a f ≤
      ENNReal.ofReal (c * M ^ p))
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder r) (hT : 0 < T) (hT1 : T ≤ 1) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) f x| ≤ c * M ^ p * T ^ a := by
  simpa only [sourceKernelFamily_pos Φ hΦ hT] using
    negativeTreeSeminorm_test_bound (sourceKernelFamily Φ hΦ) (sourceCylinder r) a f
      (mul_nonneg hc (Real.rpow_nonneg hM p)) hbudget hx hT hT1

/-- The actual ordinary forcing supremum inherits its parent negative-tree
budget; no regularity or independent smoothed supremum bound is assumed. -/
theorem source_negative_forcing_sup
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : ParabolicSpace → ℝ) {r S a c M p T : ℝ}
    (hr : 0 ≤ r) (hS : S ∈ Icc (0 : ℝ) (1 / 2)) (hrS : r ≤ S)
    (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hbudget : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) a f ≤
      ENNReal.ofReal (c * M ^ p))
    (hT : 0 < T) (hT1 : T ≤ 1) :
    sourceSup (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) f) S ≤ c * M ^ p * T ^ a := by
  apply csSup_le ((sourceCylinder_nonempty hS).image _)
  rintro z ⟨x, hx, rfl⟩
  exact source_negative_forcing_test Φ hΦ f hc hM hbudget
    (sourceCylinder_antitone hr hrS hx) hT hT1

/-- The complete B forcing is controlled by its actual recentered forcing
and the ordinary V tree budget, with parent amplitude M. -/
theorem source_complete_forcing_bound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ) (hv : Continuous v) (hV : Continuous V)
    (C₂ : ℝ) {r a c p T : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hbudget : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) a V ≤
      ENNReal.ofReal (c * sourceSup v r ^ p))
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder r) (hT : 0 < T) (hT1 : T ≤ 1) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    |pastSmooth μ (fun y => v y * V y) x + 3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)| ≤
      |pastSmooth μ (fun y => (v y - v x) * V y) x +
        3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)| +
      sourceSup v r * (c * sourceSup v r ^ p * T ^ a) := by
  have hM := (abs_nonneg (v x)).trans (abs_le_sourceSup hv hr hx)
  dsimp only
  rw [source_complete_forcing_recenter Φ hΦ v J V hv hV C₂ x hT hT1]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_mul]
  exact mul_le_mul (abs_le_sourceSup hv hr hx)
    (source_negative_forcing_test Φ hΦ V hc hM hbudget hx hT hT1)
    (abs_nonneg _) hM

end GlobalPhi43.MW20
