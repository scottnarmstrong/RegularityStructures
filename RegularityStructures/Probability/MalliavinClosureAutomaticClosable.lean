/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureClosable

/-!
# Automatic closability of the cylindrical white-noise derivative

The smooth finite-rank test-field adjoint is an explicit `L²` random variable.  Combining that
adjoint with the finite-dimensional Gaussian integration-by-parts identity removes the auxiliary
duality hypothesis from the graph closability argument.  Thus a sequence of cylindrical graph
points converging to `(0,G)` has `G = 0`, which is the closability statement in [HS23,
Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

theorem malliavin_derivative_closable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W)
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    (q : ℕ → Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P))
    (hq : ∀ n, q n ∈ cylindricalMalliavinGraph P W)
    (hvalue : Tendsto (fun n => (q n).1) atTop (𝓝 0))
    (hderivative : Tendsto (fun n => (q n).2) atTop (𝓝 G)) :
    G = 0 := by
  apply malliavin_derivative_closable_on_smooth_tests hW q hq hvalue hderivative
  intro V hV
  rcases hV with ⟨m, r, a, u, k, ha, hu_cont, hu_support, hu_lp, hk, hsum, hV_eq⟩
  obtain ⟨R, hR, hR_eq, hRj⟩ := malliavin_smooth_test_adjoint
    hW ha hu_cont hu_support hu_lp hk
  refine ⟨hR.toLp R, ?_⟩
  intro n
  rcases hq n with ⟨l, h, f, hmem, hcont, hgrowth, hF, hD, hq_eq⟩
  rw [hV_eq, hq_eq]
  exact malliavin_graph_pairing_smooth_test hW hmem hcont hgrowth hF hD
    ha hu_cont hu_support hu_lp hk hsum hR hR_eq hRj

end RegularityStructures

end
