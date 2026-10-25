/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureGraphDuality
public import RegularityStructures.Probability.MalliavinClosureTestFields
public import RegularityStructures.Probability.MalliavinClosureRelativeClosability

/-!
# Closability on the smooth-test closure

The derivative component of every cylindrical graph point lies in the closure of the smooth
finite-rank test fields.  Consequently a graph sequence converging to `(0,G)` has `G` in that
same closed subspace.  If its fixed-test duality is supplied explicitly, continuity of the `L²`
pairing gives `G = 0`.  This is the white-noise closability step underlying
[HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

theorem malliavin_derivative_closable_on_smooth_tests
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W)
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    (q : ℕ → Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P))
    (hq : ∀ n, q n ∈ cylindricalMalliavinGraph P W)
    (hvalue : Tendsto (fun n => (q n).1) atTop (𝓝 0))
    (hderivative : Tendsto (fun n => (q n).2) atTop (𝓝 G))
    (hdual : ∀ V, V ∈ malliavinSmoothTestFieldSet P W →
      ∃ K : Lp ℝ 2 P, ∀ n,
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing
            (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V =
          (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 K) :
    G = 0 := by
  let S := malliavinSmoothTestFieldSet P W
  have hq_closure : ∀ n, (q n).2 ∈ closure S := by
    intro n
    rcases hq n with ⟨n', h, f, hmem, hcont, hgrowth, hF, hD, hqeq⟩
    rw [hqeq]
    exact malliavin_cylindricalDerivative_mem_closure_smooth_test_fields
      hW hmem hcont hgrowth hD
  have hG_closure : G ∈ closure S := by
    apply (isClosed_closure : IsClosed (closure S)).mem_of_tendsto hderivative
    exact Filter.Eventually.of_forall hq_closure
  apply malliavin_zero_of_closure_duality hG_closure
  intro V hV
  obtain ⟨K, hK⟩ := hdual V hV
  have hleft : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 G V)) := by
    have hp := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (whiteNoiseDerivativeMeasure P) 2 2).continuous₂.comp₂ continuous_fst continuous_snd
    have hprod : Tendsto (fun n => ((q n).2, V)) atTop (𝓝 (G, V)) := by
      rw [nhds_prod_eq]
      exact hderivative.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => V) atTop (𝓝 V))
    have ht := (hp.tendsto (G, V)).comp hprod
    change Tendsto (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 G V)) at ht
    exact ht
  have hright : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 K) atTop
      (𝓝 0) := by
    have hp := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2).continuous₂.comp₂
      continuous_fst continuous_snd
    have hprod : Tendsto (fun n => ((q n).1, K)) atTop (𝓝 (0, K)) := by
      rw [nhds_prod_eq]
      exact hvalue.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K))
    have ht := (hp.tendsto (0, K)).comp hprod
    have hzero : (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 0 K = 0 := by
      simp
    have hfun :
        ((fun w : Lp ℝ 2 P × Lp ℝ 2 P =>
          Function.uncurry (fun x y =>
            (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 x y) (w.1, w.2)) ∘
          (fun n => ((q n).1, K))) =
        (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 K) := by
      funext n
      rfl
    rw [hfun] at ht
    simpa [hzero] using ht
  have hlim : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop (𝓝 0) := by
    rw [show (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) =
        (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 K) by
      funext n
      exact hK n]
    exact hright
  exact tendsto_nhds_unique hleft hlim

end RegularityStructures

end
