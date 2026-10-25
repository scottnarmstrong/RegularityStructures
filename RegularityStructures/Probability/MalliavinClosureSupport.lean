/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureLinearity
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option linter.style.haveILetI false

/-!
# Full support of the standard Gaussian law

The standard Gaussian product measure is positive on every nonempty open set.  Thus a continuous
function which vanishes almost everywhere under that law vanishes everywhere.  This support fact
is the finite-dimensional step used to turn equality of cylindrical functionals into equality of
their derivatives along the Gaussian support.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem standardGaussian_continuous_ae_eq_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : Continuous f) (hzero : f =ᵐ[standardGaussianMeasure n] 0) : f = 0 := by
  let μ : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hμopen (i : Fin n) : Measure.IsOpenPosMeasure (μ i) := by
    exact (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
  change f =ᵐ[Measure.pi μ] 0 at hzero
  letI : Measure.IsOpenPosMeasure (Measure.pi μ) := by
    constructor
    rintro U hU ⟨a, ha⟩
    obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 hU a ha
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
    simp only [Measure.pi_pi]
    rw [CanonicallyOrderedAdd.prod_pos]
    intro i hi
    letI : Measure.IsOpenPosMeasure (μ i) := hμopen i
    apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩
  exact (Continuous.ae_eq_iff_eq (Measure.pi μ) hcont continuous_zero).mp hzero

end RegularityStructures

end
