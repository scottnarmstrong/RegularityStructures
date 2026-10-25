/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Explicit periodic Littlewood--Paley blocks

For the comparison with the heat norm (2.3) of the statement, choose a smooth one-dimensional cutoff
equal to one on `[-1,1]` and zero outside `(-2,2)`, and take its tensor product in Fourier space.
The low-frequency symbol at level `n` is the cutoff at frequency scale `2^n`; consecutive
differences give the dyadic blocks. The finite frequency box contains the whole support of each
symbol.

These are literal Fourier multiplier formulas, using Mathlib's normalized torus Fourier
coefficients. The extended norm is the standard inhomogeneous `B^η_{∞,∞}` dyadic expression
for this fixed cutoff; this module does not yet prove equivalence with the heat norm.
-/

@[expose] public noncomputable section

open scoped ENNReal
open UnitAddTorus

namespace RegularityStructures

/-- A fixed smooth cutoff with inner radius one and outer radius two. -/
def torusLPBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

/-- The tensor-product low-frequency symbol at frequency scale `2^n`. -/
def torusLowFrequencySymbol (n : ℕ) (k : Fin 3 → ℤ) : ℝ :=
  ∏ i : Fin 3, torusLPBump (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ))

/-- Low frequencies at level zero, then consecutive low-frequency differences. -/
def torusDyadicFrequencySymbol : ℕ → (Fin 3 → ℤ) → ℝ
  | 0, k => torusLowFrequencySymbol 0 k
  | n + 1, k => torusLowFrequencySymbol (n + 1) k - torusLowFrequencySymbol n k

/-- A finite integer-frequency cube containing the level-`n` symbol support. -/
def torusLPFrequencyBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 =>
    Finset.Icc (-((2 ^ (n + 1) : ℕ) : ℤ)) ((2 ^ (n + 1) : ℕ) : ℤ)

/-- The periodic dyadic block as a finite Fourier multiplier on a real continuous function. -/
def torusLittlewoodPaleyBlock (n : ℕ) (f : C(Torus3, ℝ)) : C(Torus3, ℂ) :=
  ∑ k ∈ torusLPFrequencyBox n,
    ((torusDyadicFrequencySymbol n k : ℂ) *
      mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k) • mFourier k

/-- The inhomogeneous periodic `B^η_{∞,∞}` extended norm for the fixed smooth dyadic cutoff. -/
def torusLittlewoodPaleyENorm (η : ℝ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * η)) * ‖torusLittlewoodPaleyBlock n f‖ₑ

theorem torusDyadicFrequencySymbol_zero (k : Fin 3 → ℤ) :
    torusDyadicFrequencySymbol 0 k = torusLowFrequencySymbol 0 k := rfl

theorem torusDyadicFrequencySymbol_succ (n : ℕ) (k : Fin 3 → ℤ) :
    torusDyadicFrequencySymbol (n + 1) k =
      torusLowFrequencySymbol (n + 1) k - torusLowFrequencySymbol n k := rfl

theorem sum_torusDyadicFrequencySymbol (n : ℕ) (k : Fin 3 → ℤ) :
    ∑ j ∈ Finset.range (n + 1), torusDyadicFrequencySymbol j k =
      torusLowFrequencySymbol n k := by
  induction n with
  | zero => simp only [zero_add, Finset.sum_range_one, torusDyadicFrequencySymbol_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, torusDyadicFrequencySymbol_succ]
    ring

theorem torusLowFrequencySymbol_eq_one (n : ℕ) (k : Fin 3 → ℤ)
    (hk : ∀ i, |(k i : ℝ)| ≤ (2 : ℝ) ^ n) : torusLowFrequencySymbol n k = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply torusLPBump.one_of_mem_closedBall
  change dist (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ)) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  calc
    ((2 : ℝ) ^ n)⁻¹ * |(k i : ℝ)| ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left (hk i) (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

theorem torusLowFrequencySymbol_eq_zero_of_large_coord (n : ℕ) (k : Fin 3 → ℤ)
    (i : Fin 3) (hk : (2 : ℝ) ^ (n + 1) ≤ |(k i : ℝ)|) :
    torusLowFrequencySymbol n k = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply torusLPBump.zero_of_le_dist
  change 2 ≤ dist (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ)) 0
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  calc
    (2 : ℝ) = ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * |(k i : ℝ)| :=
      mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr (pow_nonneg (by norm_num) _))

theorem torusDyadicFrequencySymbol_eq_zero_of_notMem_box
    (n : ℕ) (k : Fin 3 → ℤ) (hk : k ∉ torusLPFrequencyBox n) :
    torusDyadicFrequencySymbol n k = 0 := by
  have hex : ∃ i, (2 : ℝ) ^ (n + 1) < |(k i : ℝ)| := by
    by_contra! h
    apply hk
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (abs_le.mp (h i)).1
    · exact_mod_cast (abs_le.mp (h i)).2
  obtain ⟨i, hi⟩ := hex
  cases n with
  | zero => exact torusLowFrequencySymbol_eq_zero_of_large_coord 0 k i hi.le
  | succ n =>
    rw [torusDyadicFrequencySymbol_succ,
      torusLowFrequencySymbol_eq_zero_of_large_coord (n + 1) k i hi.le]
    have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1 + 1) := by
      conv_rhs => rw [pow_succ]
      linarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)]
    rw [torusLowFrequencySymbol_eq_zero_of_large_coord n k i (hpow.trans hi.le), sub_zero]

end RegularityStructures

end
