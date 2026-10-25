/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Space-time white noise

A space-time white noise on `ℝ × T³` is a family `(W(h))` of real random variables, indexed by
square-integrable functions `h`, such that every finite subfamily is a centred Gaussian vector with
covariance `E[W(hᵢ) W(hⱼ)] = ∫ hᵢ hⱼ` (the statement, Definition 2.2).

Measurability is stated explicitly. In Mathlib, `Measure.map` of a non-measurable map is a point
mass, which counts as Gaussian, and the Bochner integral of a non-measurable function is zero.
Without the measurability clauses, a non-measurable family could satisfy the remaining conditions.

Source: the statement, Definition 2.2.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X` is a centred Gaussian vector in `ℝⁿ` with covariance matrix `C` under `P`: it is
a.e.-measurable, its law is Gaussian, and it has mean zero and covariance `C`. -/
def IsCentredGaussianVector (P : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ)
    (C : Fin n → Fin n → ℝ) : Prop :=
  AEMeasurable X P ∧ ProbabilityTheory.IsGaussian (P.map X) ∧ (∀ i, ∫ ω, X ω i ∂P = 0) ∧
    ∀ i j, ∫ ω, X ω i * X ω j ∂P = C i j

/-- `W` is a space-time white noise on `ℝ × T³` under `P`: each `W h` with `h` square-integrable
is a random variable, and every finite family is a centred Gaussian vector with covariance
`∫ hᵢ hⱼ`. -/
def IsWhiteNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) : Prop :=
  (∀ h : SpaceTime → ℝ, MemLp h 2 → Measurable (W h)) ∧
    ∀ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) →
      IsCentredGaussianVector P (fun ω i => W (h i) ω) fun i j => ∫ z, h i z * h j z

end RegularityStructures

end
