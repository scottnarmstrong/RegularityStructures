module

public import GlobalPhi43.MW20.AugmentedMaximumRow
public import GlobalPhi43.MW20.SourceSmoothingError

/-!
# The augmented unsmoothed maximum row MW20 (4.29)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- MW20 (4.29), with actual Hölder and forcing seminorms, obtained from
(4.28) and the proved actual-kernel smoothing error. -/
theorem mw20_augmented_row_4_29 (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v J V W e : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    (hJ : ContinuousOn J sourceClosedCylinder) (hV : ContinuousOn V sourceClosedCylinder)
    (hW : ContinuousOn W sourceClosedCylinder)
    (he : ContinuousOn e sourceClosedCylinder) (C₂ : ℝ)
    (hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    {T S R α E₁ : ℝ}
    (he₁ : ∀ z ∈ sourceCylinder 0, |e z| ≤ E₁) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hT : 0 < T) (hTS : T < S) (hSR : S < R) (hR : R ≤ 1 / 2) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    let A := pastSmooth μ (fun z => v z ^ 2 * J z)
    let B := fun z => pastSmooth μ (fun y => v y * V y) z +
      3 * C₂ * (pastSmooth μ v z + pastSmooth μ J z)
    let C := pastSmooth μ W
    let D := fun z => (pastSmooth μ v z) ^ 3 - pastSmooth μ (fun y => v y ^ 3) z
    sourceSup v R ≤ 46 * max
      (sourceHolder v α (R - T) (2 * T) * T ^ α)
      (max (1 / (R - S)) (max (fourForcingRoot A B C D S) (E₁ ^ (1 / 3 : ℝ)))) := by
  have hm := mw20_augmented_row_4_28 Φ hΦ hv hJ hV hW he C₂ hPDE he₁ hT hTS hSR hR
  have he := sourceSup_le_smoothed_add_error Φ hΦ hv hT (hTS.trans hSR) hR hα0 hα1
  have hcombine {a b E M : ℝ} (ha : a ≤ b + E) (hb : b ≤ 45 * M) :
      a ≤ 46 * max E M := by
    nlinarith [le_max_left E M, le_max_right E M]
  exact hcombine he hm

end GlobalPhi43.MW20
