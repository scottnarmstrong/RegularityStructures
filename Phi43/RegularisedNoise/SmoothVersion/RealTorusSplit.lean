/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.TorusSeries

/-!
# Real Fourier series with separate cosine and sine families

A white noise is evaluated on real test functions.  This module splits the real Fourier
series into the real and imaginary character families, so that the two families can be indexed by
`Sum (d → ℤ) (d → ℤ)` and used directly in a real random series.
-/

@[expose] public noncomputable section

open Complex

namespace RegularityStructures.Phi43

variable {d : Type*} [Fintype d]

def realTorusFourierSplitTerm (f : C(UnitAddTorus d, ℝ))
    (k : Sum (d → ℤ) (d → ℤ)) (x : UnitAddTorus d) : ℝ :=
  match k with
  | Sum.inl n =>
      (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) n).re *
        (UnitAddTorus.mFourier n x).re
  | Sum.inr n =>
      -((UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) n).im *
        (UnitAddTorus.mFourier n x).im)

theorem hasSum_realTorusFourierSplitTerm
    (f : C(UnitAddTorus d, ℝ)) (x : UnitAddTorus d)
    (h : Summable (fun k : d → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖)) :
    HasSum (fun k => realTorusFourierSplitTerm f k x) (f x) := by
  let left : (d → ℤ) → ℝ := fun k =>
    (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re *
      (UnitAddTorus.mFourier k x).re
  let right : (d → ℤ) → ℝ := fun k =>
    -((UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im *
      (UnitAddTorus.mFourier k x).im)
  have hleft : Summable (fun k : d → ℤ =>
      (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re *
        (UnitAddTorus.mFourier k x).re) := by
    apply Summable.of_norm_bounded h
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    have hm : ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k x‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          ContinuousMap.norm_coe_le_norm _ _
        _ = 1 := UnitAddTorus.mFourier_norm
    calc
      |(UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re| *
          |(UnitAddTorus.mFourier k x).re| ≤
          ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ *
            ‖UnitAddTorus.mFourier k x‖ :=
        mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ * 1 :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ := mul_one _
  have hright : Summable (fun k : d → ℤ =>
      -((UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im *
        (UnitAddTorus.mFourier k x).im)) := by
    apply Summable.of_norm_bounded h
    intro k
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    have hm : ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k x‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          ContinuousMap.norm_coe_le_norm _ _
        _ = 1 := UnitAddTorus.mFourier_norm
    calc
      |(UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im| *
          |(UnitAddTorus.mFourier k x).im| ≤
          ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ *
            ‖UnitAddTorus.mFourier k x‖ :=
        mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _)
          (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ * 1 :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖ := mul_one _
  have hsplit : HasSum (fun k : d → ℤ =>
      (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re *
        (UnitAddTorus.mFourier k x).re -
      (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im *
        (UnitAddTorus.mFourier k x).im) (f x) :=
    hasSum_realTorusFourierTerm_of_summable f x h
  have hsum : HasSum (fun k : d → ℤ =>
      (UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).re *
        (UnitAddTorus.mFourier k x).re +
      -((UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k).im *
        (UnitAddTorus.mFourier k x).im))
      ((∑' k, left k) + (∑' k, right k)) := by
    exact hleft.hasSum.add hright.hasSum
  have hlimit :
      ((∑' k, left k) + (∑' k, right k)) = f x := by
    exact hsum.unique hsplit
  have hsumSplit :
      HasSum (fun k : Sum (d → ℤ) (d → ℤ) => realTorusFourierSplitTerm f k x)
        ((∑' k, left k) + (∑' k, right k)) := by
    apply HasSum.sum
    · simpa [Function.comp_def, realTorusFourierSplitTerm, left] using hleft.hasSum
    · simpa [Function.comp_def, realTorusFourierSplitTerm, right] using hright.hasSum
  rw [hlimit] at hsumSplit
  exact hsumSplit

end RegularityStructures.Phi43

end
