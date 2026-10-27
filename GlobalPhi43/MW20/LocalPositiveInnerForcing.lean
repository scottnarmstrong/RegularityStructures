module

public import GlobalPhi43.MW20.LocalPositiveOnePoint
public import GlobalPhi43.MW20.LocalPositiveBudgets
public import GlobalPhi43.Local.RadiusGeometry

/-! Small-test formal forcing at every original interior centre. Ball
containment is derived, not supplied. No PDE premise occurs. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_formal_one_point_inner_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r d T L ε c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hT : 0 < T)
    (hTL : T ≤ L) (hLd : L ≤ d / 8) (hε : 0 < ε) (hsmall : ε < 1 / 14)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε)))
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
 :
    let Q := localScalarSup (sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x) (Local.pastBall x L)
    Q ≠ ⊤ ∧ T ^ 2 * Q.toReal ≤ sourceOnePointCoefficient v Y Z ε r (d / 4) L c *
        (∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a)) := by
  have hxQ : x ∈ Local.cylinderInterior r (d / 4) :=
    Local.cylinderInterior_mono (by positivity) (by linarith) hx
  have hball : Local.pastBall x (L + T) ⊆ Local.cylinderInterior r (d / 4) :=
    Local.pastBall_subset_interior (by positivity) (by linarith) (by linarith) hx
  exact source_formal_one_point_positive Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV
    hr (by positivity) hT hTL (by linarith) hε hsmall hc hc1
    hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD hxQ hball


end GlobalPhi43.MW20
