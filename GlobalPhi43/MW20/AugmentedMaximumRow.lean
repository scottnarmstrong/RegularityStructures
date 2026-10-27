module

public import GlobalPhi43.MW20.AugmentedConvolvedEquation
public import GlobalPhi43.MW20.AugmentedFourForcingMaximum
public import GlobalPhi43.MW20.BoundedSourceFields

/-!
# The actual augmented maximum-principle row MW20 (4.28)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Augmented MW20 (4.28), with actual source suprema of the four actual smoothed
forcing fields, including the complete renormalized second product. -/
theorem mw20_augmented_row_4_28 (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v J V W e : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    (hJ : ContinuousOn J sourceClosedCylinder) (hV : ContinuousOn V sourceClosedCylinder)
    (hW : ContinuousOn W sourceClosedCylinder)
    (he : ContinuousOn e sourceClosedCylinder) (C₂ : ℝ)
    (hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    {T S R E₁ : ℝ} (he₁ : ∀ z ∈ sourceCylinder 0, |e z| ≤ E₁) (hT : 0 < T) (hTS : T < S) (hSR : S < R) (hR : R ≤ 1 / 2) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    let w := pastSmooth μ v
    let A := pastSmooth μ (fun z => v z ^ 2 * J z)
    let B := fun z => pastSmooth μ (fun y => v y * V y) z +
      3 * C₂ * (pastSmooth μ v z + pastSmooth μ J z)
    let C := pastSmooth μ W
    let D := fun z => (pastSmooth μ v z) ^ 3 - pastSmooth μ (fun y => v y ^ 3) z
    sourceSup w R ≤ 45 * max (1 / (R - S))
      (max (fourForcingRoot A B C D S) (E₁ ^ (1 / 3 : ℝ))) := by
  let μ := infiniteKernelMeasure Φ hΦ T hT
  let w := pastSmooth μ v
  let A := pastSmooth μ (fun z => v z ^ 2 * J z)
  let B := fun z => pastSmooth μ (fun y => v y * V y) z +
    3 * C₂ * (pastSmooth μ v z + pastSmooth μ J z)
  let C := pastSmooth μ W
  let D := fun z => (pastSmooth μ v z) ^ 3 - pastSmooth μ (fun y => v y ^ 3) z
  have hT1 : T ≤ 1 := by linarith
  have hbounded (f : ParabolicSpace → ℝ) (hf : ContinuousOn f sourceClosedCylinder) :
      BddAbove ((fun z => |pastSmooth μ f z|) '' sourceCylinder S) := by
    simpa only [pastSmooth, μ] using sourceSup_bddAbove_pastSmooth Φ hΦ f hf hT hT1 hTS.le
  have hA : BddAbove ((fun z => |A z|) '' sourceCylinder S) :=
    hbounded _ ((hv.continuous.pow 2).mul hJ)
  have hB : BddAbove ((fun z => |B z|) '' sourceCylinder S) :=
    sourceSup_bddAbove_add (hbounded _ (hv.continuous.mul hV))
      (sourceSup_bddAbove_const_mul
        (sourceSup_bddAbove_add (hbounded _ hv.continuous) (hbounded _ hJ)) (3 * C₂))
  have hC : BddAbove ((fun z => |C z|) '' sourceCylinder S) := hbounded _ hW
  have hD : BddAbove ((fun z => |D z|) '' sourceCylinder S) :=
    sourceSup_bddAbove_sub (sourceSup_bddAbove_pow (hbounded _ hv.continuous) 3)
      (hbounded _ (hv.continuous.pow 3))
  have hE := hbounded e he
  have hw : ∀ z ∈ sourceCylinder S, ContDiffAt ℝ 2 w z := fun z hz =>
    pastSmooth_infiniteKernel_contDiffAt_two Φ hΦ hv hT hT1 hTS hz
  have hp : ∀ z ∈ sourceCylinder S,
      sourceHeat w z = -w z ^ 3 - 3 * A z - 3 * B z - C z + D z - pastSmooth μ e z := by
    intro z hz
    have h := mw20_augmented_row_4_27 Φ hΦ hv hJ hV hW he C₂ hPDE hT hT1 hTS hz
    dsimp only at h
    dsimp [w, A, B, C, D, μ]
    linear_combination h
  have hbound : sourceSup (pastSmooth μ e) S ≤ E₁ := by
    apply csSup_le ((sourceCylinder_nonempty ⟨hT.le.trans hTS.le, hSR.le.trans hR⟩).image _)
    rintro b ⟨x, hx, rfl⟩
    exact source_smoothed_defect_le Φ hΦ e hT hT1 hTS.le he₁ hx
  have hroot := Real.rpow_le_rpow
    (sourceSup_nonneg_of_bddAbove _ ⟨hT.le.trans hTS.le, hSR.le.trans hR⟩ hE)
    hbound (by norm_num : (0 : ℝ) ≤ 1 / 3)
  exact (source_augmented_four_forcing_maximum w A B C D (pastSmooth μ e)
    (hT.le.trans hTS.le) hSR hR hw hA hB hC hD hE hp).trans
    (mul_le_mul_of_nonneg_left (max_le_max le_rfl (max_le_max le_rfl hroot)) (by norm_num))

end GlobalPhi43.MW20
