/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovSupMoment
public import RegularityStructures.Torus.KolmogorovHolderBesovCriterion
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The annealed dyadic finite-net criterion

This file contains the stochastic part of the parabolic Kolmogorov argument.  At scale `n`, a
finite spatial net contributes one random coordinate for each net point and the smoothing
estimate contributes a second finite family of increment coordinates.  The hypotheses below are
only annealed, pointwise estimates for those coordinates.  A separate deterministic inequality
`hblock` is the semigroup/net estimate: it says that the supremum over the whole dyadic block is
bounded by the two finite-net envelopes.  Thus no random pathwise Besov bound is hidden in the
statement.

For a parabolic compact in `ℝ × T³`, a net at radius `2⁻ⁿ/ell` has cardinality of order
`2^(5 n / ell)`.  Combining that covering factor with a pointwise bound of order
`2^(-α p n / ell)` gives the geometric summability condition `p (α - α') > 5`, exactly the
exponent in Hairer [Hai14, Proposition 3.32 and Theorem 10.7].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

/-- The same finite-family estimate for an arbitrary finite index type. -/
def finiteFamilyEnvelope {Ω : Type*} {ι : Type*} [Fintype ι]
    (V : Ω → ι → ℝ≥0∞) : Ω → ℝ≥0∞ := fun ω => ∑ j, V ω j

theorem finiteFamilyEnvelope_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ι : Type*} [Fintype ι] {V : Ω → ι → ℝ≥0∞}
    (hV : ∀ j, AEMeasurable (fun ω => V ω j) P) :
    AEMeasurable (finiteFamilyEnvelope V) P := by
  exact Finset.aemeasurable_fun_sum Finset.univ fun j _ => hV j

theorem finiteFamilyEnvelope_moment_le_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
    {p : ℕ} {V : Ω → ι → ℝ≥0∞} {b : ι → ℝ≥0∞}
    (hp : 1 ≤ p) (hV : ∀ j, AEMeasurable (fun ω => V ω j) P)
    (hpoint : ∀ j, ∫⁻ ω, (V ω j) ^ p ∂P ≤ b j) :
    ∫⁻ ω, (finiteFamilyEnvelope V ω) ^ p ∂P ≤
      (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ j, b j := by
  have hpow : ∀ ω,
      (finiteFamilyEnvelope V ω) ^ p ≤
        (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ j, (V ω j) ^ p := by
    intro ω
    simpa [finiteFamilyEnvelope, ENNReal.rpow_natCast, Finset.card_univ] using
      (ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset ι)
        (fun j => V ω j) (p := (p : ℝ)) (by exact_mod_cast hp))
  have hsum : AEMeasurable
      (fun ω => ∑ j, (V ω j) ^ p) P := by
    exact Finset.aemeasurable_fun_sum Finset.univ fun j _ => (hV j).pow_const p
  calc
    ∫⁻ ω, (finiteFamilyEnvelope V ω) ^ p ∂P ≤
        ∫⁻ ω, (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ j, (V ω j) ^ p ∂P := lintegral_mono hpow
    _ = (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∫⁻ ω, ∑ j, (V ω j) ^ p ∂P := lintegral_const_mul'' _ hsum
    _ = (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ j,
        ∫⁻ ω, (V ω j) ^ p ∂P := by
      rw [MeasureTheory.lintegral_finsetSum' Finset.univ
        (fun j _ => (hV j).pow_const p)]
    _ ≤ (Fintype.card ι : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ j, b j := by
      gcongr with j
      exact hpoint j

/-!
The next declaration exposes the pointwise form used in applications.  The two displayed
coordinate estimates are exactly the annealed hypotheses; `hscale` is a deterministic arithmetic
condition on the net cardinality and the scale decay, not a random Besov estimate.
-/

end RegularityStructures

end
