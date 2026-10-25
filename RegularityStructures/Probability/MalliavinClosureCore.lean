/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoiseSpectralGap
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The cylindrical graph and its Malliavin closure

The derivative of a cylindrical white-noise functional is an element of the product `L²` space
over `P.prod volume`.  This file defines the graph of the explicitly integrable cylindrical
representations and its closure.  The latter is the Sobolev space `D^{1,2}` used below.  The
definition is deliberately made at the `Lp` level, so null-set representatives do not enter the
closure construction.

The cylindrical core is the class of functionals from [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The measure on the space-time variable of a white-noise derivative. -/
def whiteNoiseDerivativeMeasure (P : Measure Ω) : Measure (Ω × SpaceTime) :=
  P.prod (volume : Measure SpaceTime)

/-- The graph of the explicitly `L²` cylindrical functionals and their derivatives. -/
def cylindricalMalliavinGraph (P : Measure Ω)
    (W : (SpaceTime → ℝ) → Ω → ℝ) :
    Set (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) :=
  {q | ∃ (n : ℕ) (h : Fin n → SpaceTime → ℝ) (f : (Fin n → ℝ) → ℝ)
      (hmem : ∀ i, MemLp (h i) 2)
      (hcont : ContDiff ℝ 1 f)
      (hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
        ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
      (hF : MemLp (cylindricalFunctional W h f) 2 P)
      (hD : MemLp (fun p : Ω × SpaceTime =>
        cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P)),
      q = (hF.toLp (cylindricalFunctional W h f),
        hD.toLp (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2))}

/-- The closed graph defining the white-noise Malliavin-Sobolev space `D^{1,2}`. -/
def MalliavinSobolev (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) :=
  closure (cylindricalMalliavinGraph P W)

/-- The value component of an element of `D^{1,2}`. -/
def malliavinValue {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (u : MalliavinSobolev P W) : Lp ℝ 2 P :=
  u.1.1

/-- The derivative component of an element of `D^{1,2}`. -/
def malliavinDerivative {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (u : MalliavinSobolev P W) : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) :=
  u.1.2

theorem malliavinValue_coe {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (u : MalliavinSobolev P W) :
    (malliavinValue u : Ω → ℝ) =ᵐ[P] u.1.1 := by
  exact Filter.Eventually.of_forall (fun ω => rfl)

theorem malliavinDerivative_coe {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (u : MalliavinSobolev P W) :
    (malliavinDerivative u : Ω × SpaceTime → ℝ) =ᵐ[whiteNoiseDerivativeMeasure P]
      u.1.2 := by
  exact Filter.Eventually.of_forall (fun p => rfl)

theorem cylindricalMalliavinGraph_mem_closure {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {q : Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    (hq : q ∈ cylindricalMalliavinGraph P W) :
    q ∈ MalliavinSobolev P W := by
  exact subset_closure hq

end RegularityStructures

end
