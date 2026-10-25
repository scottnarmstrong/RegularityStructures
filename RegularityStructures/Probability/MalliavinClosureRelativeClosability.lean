/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureClosability

/-!
# Relative duality criterion for Malliavin closability

For a convergent graph sequence, the limiting derivative already belongs to the closure of the
cylindrical derivative test set.  Thus closability only needs the Gaussian duality identity on that
test set, rather than a density assertion in the whole product `L²` space.  This is the exact
functional-analytic reduction used for the `D^{1,2}` closure in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

theorem malliavin_zero_of_closure_duality
    {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    {S : Set (Lp ℝ 2 (whiteNoiseDerivativeMeasure P))}
    (hG : G ∈ closure S)
    (hdual : ∀ V, V ∈ S →
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (whiteNoiseDerivativeMeasure P) 2 2 G V = 0) :
    G = 0 := by
  let ℓ : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (whiteNoiseDerivativeMeasure P) 2 2) G
  have hclosed : IsClosed {V | ℓ V = 0} := by
    exact isClosed_eq ℓ.continuous continuous_const
  have hsubset : S ⊆ {V | ℓ V = 0} := by
    intro V hV
    exact hdual V hV
  have hclsubset : closure S ⊆ {V | ℓ V = 0} := by
    calc
      closure S ⊆ closure {V | ℓ V = 0} := closure_mono hsubset
      _ = {V | ℓ V = 0} := hclosed.closure_eq
  have hzero : ℓ G = 0 := hclsubset hG
  have hnorm : ‖G‖ ^ 2 = 0 := by
    calc
      ‖G‖ ^ 2 = (ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (whiteNoiseDerivativeMeasure P) 2 2 G G :=
        (malliavinLpPairing_self_eq_norm_sq).symm
      _ = 0 := hzero
  have : ‖G‖ = 0 := (sq_eq_zero_iff).mp hnorm
  exact norm_eq_zero.mp this

end RegularityStructures

end
