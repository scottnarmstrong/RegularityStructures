/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity

/-!
# Mollifying a `Q`-family on `ℝ⁴` by its test-function pairings

Let `D` be a `Q`-family for the auxiliary semigroup on `ℝ⁴` with measurable regularisations and
the Besov-type bound `|D_u| ≤ C u^{α/4}` (`0 < u ≤ 1`, `α > -4`), and let `φ ∈ B^4`. Then:

* `tendsto_integral_rescaledTestFunction`, `abs_integral_rescaledTestFunction_le`: the pairing
  `⟨D, φ^c_w⟩` exists for every `c > 0`, `w`, and `|∫ D_s φ^c_w| ≤ C r4PairingConst α c`
  uniformly in `0 < s ≤ 1` and `w`;
* `integral_kernel_mul_integral_eq` (Fubini and translation invariance):
  `∫_w q_t(x − w) (∫_y D_s(y) ρ(y − w) dy) dw = ∫_v ρ(v) D_{t+s}(x + v) dv`;
* `integral_rescaledTestFunction_mul_eq` (the limit `s ↓ 0`, using the right-continuity of
  `t ↦ D_t`): **`∫_v φ^c_0(v) D_t(x + v) dv = ∫_w q_t(x − w) ⟨D, φ^c_w⟩ dw`**, i.e. the
  mollification of `D_t` at scale `c` is the `Q_t`-average of the pairings with the rescaled test
  functions.

These are the inputs of the uniqueness of admissible `Q`-families on `ℝ⁴` with given pairings
against rescaled test functions.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

theorem isGeneratorPair_rescaledTestFunction {φ : ParabolicSpace → ℝ}
    (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    parabolicSemigroup.IsGeneratorPair (rescaledTestFunction φ c z)
      (parabolicGenerator (rescaledTestFunction φ c z)) :=
  parabolicSemigroup_isGeneratorPair (contDiff_rescaledTestFunction_of_mem hφ c z)
    (hasCompactSupport_rescaledTestFunction hφ hc z)

end RegularityStructures

end
