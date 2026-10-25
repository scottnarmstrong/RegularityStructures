/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Real form of an absolutely convergent torus Fourier series

The windowed white-noise construction uses real test functions, while Mathlib's multivariate
Fourier basis is complex-valued.  This file records the small real/complex bridge: an absolutely
summable complex Fourier series of a real continuous function can be written with the real and
imaginary parts of its coefficients and characters.  The Fourier-series input is
`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`.

This is the algebraic part of the finite-window construction of a smooth regularised
noise (Definition 2.4 of the statement); no stochastic assumptions are used here.
-/

@[expose] public noncomputable section

open Complex

namespace RegularityStructures.Phi43

variable {d : Type*} [Fintype d]

def complexifyTorusContinuousMap (f : C(UnitAddTorus d, ℝ)) : C(UnitAddTorus d, ℂ) :=
  { toFun := fun x => f x
    continuous_toFun := Complex.continuous_ofReal.comp f.continuous }

omit [Fintype d] in
@[simp]
theorem complexifyTorusContinuousMap_apply (f : C(UnitAddTorus d, ℝ))
    (x : UnitAddTorus d) : complexifyTorusContinuousMap f x = f x :=
  rfl

def realTorusFourierTerm (f : C(UnitAddTorus d, ℝ)) (k : d → ℤ)
    (x : UnitAddTorus d) : ℝ :=
  (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re *
      (UnitAddTorus.mFourier k x).re -
    (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im *
      (UnitAddTorus.mFourier k x).im

theorem hasSum_realTorusFourierTerm_of_summable
    (f : C(UnitAddTorus d, ℝ)) (x : UnitAddTorus d)
    (h : Summable (fun k : d → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖)) :
    HasSum (fun k : d → ℤ => realTorusFourierTerm f k x) (f x) := by
  have hcomplex := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := complexifyTorusContinuousMap f) h.of_norm x
  have hreal := Complex.reCLM.hasSum hcomplex
  apply hreal.congr_fun
  intro k
  unfold realTorusFourierTerm
  change _ =
    (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k •
      (UnitAddTorus.mFourier k) x).re
  change _ =
    (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k *
      (UnitAddTorus.mFourier k) x).re
  simp only [Complex.mul_re]

end RegularityStructures.Phi43

end
