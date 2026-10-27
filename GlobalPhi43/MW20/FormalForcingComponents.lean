module

public import GlobalPhi43.MW20.FormalForcingAverage
public import GlobalPhi43.MW20.SourceExpansionHeat
public import GlobalPhi43.MW20.GlobalHeatSmoothing
public import GlobalPhi43.MW20.PastBallTesting
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.SourceTestingCube
public import GlobalPhi43.MW20.SourceMixedTreeCutoff
public import GlobalPhi43.MW20.ExpansionForcingAlgebra

/-! Actual formal forcing components, before any PDE or heat substitution. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_formal_forcing_components
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v)
    (hJ : ContinuousOn J sourceClosedCylinder) (hV : ContinuousOn V sourceClosedCylinder)
    (C₂ : ℝ)
    {T L r d ε c K : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hr : 0 ≤ r) (hd : 0 < d)
    (hLK : L ≤ K) (hK1 : K ≤ 1) (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-1 - 2 * ε) V ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    {x y : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hball : Local.pastBall x (L + T) ⊆ Local.cylinderInterior r d)
    (hy : y ∈ Local.pastBall x L) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    |sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y| ≤
      sourceSup v r ^ 3 + 3 * |pastSmooth μ (fun z => v z ^ 2 * J z) y| +
        3 * (L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c *
          localSourceHolder v (1 / 2 - 3 * ε) (Local.cylinderInterior r d) K *
            sourceSup v r ^ (1 - 2 * ε)) +
        3 * |pastSmooth μ (fun z => (v z - v y) * V z) y +
          3 * C₂ * (pastSmooth μ v y + pastSmooth μ J y)| := by
  let μ := infiniteKernelMeasure Φ hΦ T hT
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hM := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hyD : y ∈ Local.cylinderInterior r d :=
    hball ⟨by linarith [hy.1], hy.2⟩
  have hcube := source_smoothed_cube_testing_ball Φ hΦ hv.continuous.continuousOn
    hT hT1 hr hd.le hball hy
  have hmixed := source_mixed_tree_cutoff Φ hΦ hv hr hd hK1
    (by linarith [Local.pdist_nonneg x y, hy.1] : 0 ≤ L) hLK
    (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε) (by linarith : (1 / 2 : ℝ) - 3 * ε ≤ 1)
    hc hM hbudgetV hx hyD hy.1.le hT hT1
  have he := sourceFormalForcingAverage_split Φ hΦ v J V C₂ hv.continuous.continuousOn
    hJ hV hT hT1 hr hd.le x hball hy
  have ha := expansion_forcing_abs
    (heat := sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y)
    (cubic := pastSmooth μ (fun z => v z ^ 3) y)
    (product := pastSmooth μ (fun z => v z ^ 2 * J z) y)
    (mixed := (v y - v x) * pastSmooth μ V y)
    (rec := pastSmooth μ (fun z => (v z - v y) * V z) y)
    (counter := C₂ * (pastSmooth μ v y + pastSmooth μ J y)) (by nlinarith only [he])
  change |sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y| ≤ _
  have hcounter : 3 * (C₂ * (pastSmooth μ v y + pastSmooth μ J y)) =
      3 * C₂ * (pastSmooth μ v y + pastSmooth μ J y) := by ring
  rw [hcounter] at ha
  nlinarith only [ha, hcube, hmixed]


end GlobalPhi43.MW20
