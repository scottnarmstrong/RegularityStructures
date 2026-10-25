/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
public import RegularityStructures.Analysis.Parabolic.Lattice.Cell

/-!
# Measurability and integrability of the pointwise reconstruction

Let `Φ = pointwiseReconstruct g f` in the window setting.

* `abs_pointwiseReconstruct_le_identDom`: `|Φ y| ≤ identDom y` (limit of `latticeAvg n`);
* `aestronglyMeasurable_pointwiseReconstruct_mul`: `Φ ψ` is a.e. strongly measurable for every
  continuous `ψ` (a limit of the continuous functions `latticeAvg n · ψ` after a cutoff by
  finite sums of cells);
* `integrable_pointwiseReconstruct_mul`: `Φ ψ` is integrable for `ψ` continuous with compact
  support;
* `hasCompactSupport_latticeCell`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

theorem hasCompactSupport_latticeCell (n : ℕ) (k : LatticeIndex) :
    HasCompactSupport (latticeCell n k) :=
  hasCompactSupport_of_eq_zero (c := 8 * ((2 : ℝ) ^ n)⁻¹) (by positivity) (latticePoint n k)
    fun w hw => by
      by_contra h
      exact absurd (parabolicNorm_sub_latticePoint_le h) (not_le.2 hw)

end RegularityStructures
