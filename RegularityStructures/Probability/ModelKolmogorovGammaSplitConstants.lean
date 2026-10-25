/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplit
public import RegularityStructures.Probability.ModelKolmogorovHSCompactRescale

/-!
# Explicit constants for the split Gamma induction

These are the finite constants produced by the unit-box telescope.  Keeping
them as definitions makes the dependence on the source constant `C` visible;
in particular, every stochastic coordinate constant carries an explicit
factor `(ENNReal.ofReal C)^r`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gammaSplitCellConstant
    (𝒯 : RegularityStructure ι) (i j : ι) (κ C : ℝ) (r : ℕ) : ℝ≥0∞ :=
  (512 : ℝ≥0∞) ^ 2 * (ENNReal.ofReal C) ^ r *
      (20 : ℝ≥0∞) ^ ((r : ℝ) *
        (𝒯.deg i - 𝒯.deg j + κ)) *
      dyadicBase 0 ^ ((r : ℝ) * κ - 10) *
      (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((r : ℝ) * κ - 10))⁻¹

def gammaSplitLeftConstant
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (κ C Cbar : ℝ) (r : ℕ) : ℝ≥0∞ := by
  classical
  exact (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
    (ENNReal.ofReal (C * 4 ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ r +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
          ENNReal.ofReal (Cbar * C *
            24 ^ (𝒯.deg i - 𝒯.deg k +
              (if (i, k) ∈ D then 0 else κ)) *
            4 ^ (𝒯.deg k - 𝒯.deg j +
              (if (k, j) ∈ D then 0 else κ))) ^ r)

def gammaSplitRightConstant
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)
    ) (i j : ι) (κ C Cbar : ℝ) (r : ℕ) : ℝ≥0∞ := by
  classical
  exact (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
    (ENNReal.ofReal (C * 4 ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ r +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
          ENNReal.ofReal (Cbar * C *
            4 ^ (𝒯.deg i - 𝒯.deg k +
              (if (i, k) ∈ D then 0 else κ)) *
            24 ^ (𝒯.deg k - 𝒯.deg j +
              (if (k, j) ∈ D then 0 else κ))) ^ r)

def gammaSplitBadConstant
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (C : ℝ) (_r : ℕ) : ℝ≥0∞ :=
  (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
      ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
        4 ^ (𝒯.deg k - 𝒯.deg j))) +
    (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
      ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
        4 ^ (𝒯.deg i - 𝒯.deg k)))

def gammaSplitGlobalConstant
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (κ C Cbar δ : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
      (gammaSplitLeftConstant 𝒯 D i j κ C Cbar r +
        gammaSplitRightConstant 𝒯 D i j κ C Cbar r)) *
    (1 - ((2 : ℝ≥0∞)⁻¹) ^
      (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹ *
    (1 - ((2 : ℝ≥0∞)⁻¹) ^
      (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹

def gammaSplitUnitConstant
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (κ C Cbar δ : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (𝒯.deg i - 𝒯.deg j)) ^ r *
    (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((r : ℝ) - 1) *
      (gammaSplitCellConstant 𝒯 i j κ C r +
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
          gammaSplitGlobalConstant 𝒯 D i j κ C Cbar δ r +
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
          gammaSplitBadConstant 𝒯 D i j C r ^ r)

def gammaSplitUnitProfile
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (κ Dbar δ : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (𝒯.deg i - 𝒯.deg j)) ^ r *
    (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((r : ℝ) - 1) *
      (gammaSplitCellConstant 𝒯 i j κ 1 r +
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
          gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r +
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
          (ENNReal.ofReal Dbar) ^ r *
            gammaSplitBadConstant 𝒯 D i j 1 r ^ r)

theorem gammaSplitUnitConstant_le_profile_mul_source
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (i j : ι) (κ C Cbar δ : ℝ) (r : ℕ)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) :
    gammaSplitUnitConstant 𝒯 D i j κ C Cbar δ r ≤
      gammaSplitUnitProfile 𝒯 D i j κ (max 1 Cbar) δ r *
        (ENNReal.ofReal C) ^ r := by
  classical
  have hCbar0 : 0 ≤ Cbar := hC.trans hCbar
  have hD0 : 0 ≤ max 1 Cbar := le_trans (by norm_num) (le_max_left _ _)
  have hCD : C ≤ max 1 Cbar := hCbar.trans (le_max_right _ _)
  have hDge : 1 ≤ max 1 Cbar := le_max_left _ _
  let Dbar : ℝ := max 1 Cbar
  have hcell : gammaSplitCellConstant 𝒯 i j κ C r =
      (ENNReal.ofReal C) ^ r * gammaSplitCellConstant 𝒯 i j κ 1 r := by
    dsimp [gammaSplitCellConstant]
    rw [ENNReal.ofReal_one]
    ring
  have hleft : gammaSplitLeftConstant 𝒯 D i j κ C Cbar r ≤
      (ENNReal.ofReal C) ^ r *
        gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r := by
    dsimp [gammaSplitLeftConstant]
    have hfirst :
        (ENNReal.ofReal (C * 4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r) ≤
          (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r := by
      rw [ENNReal.ofReal_mul hC, mul_pow]
    have hsum : ∀ k ∈ gammaGoodIntermediate 𝒯 D i j,
        ENNReal.ofReal (Cbar * C *
            24 ^ (𝒯.deg i - 𝒯.deg k +
              (if (i, k) ∈ D then 0 else κ)) *
            4 ^ (𝒯.deg k - 𝒯.deg j +
              (if (k, j) ∈ D then 0 else κ))) ^ r ≤
          (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (Dbar *
              24 ^ (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
              4 ^ (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ r := by
      intro k hk
      let a : ℝ := 24 ^ (𝒯.deg i - 𝒯.deg k +
          (if (i, k) ∈ D then 0 else κ)) *
        4 ^ (𝒯.deg k - 𝒯.deg j +
          (if (k, j) ∈ D then 0 else κ))
      have ha : 0 ≤ a := by
        dsimp [a]
        positivity
      have hmul : Cbar * C * a ≤ C * (Dbar * a) := by
        calc
          Cbar * C * a = C * (Cbar * a) := by ring
          _ ≤ C * (Dbar * a) := by
            gcongr
            exact show Cbar ≤ Dbar by dsimp [Dbar]; exact le_max_right _ _
      have hnonneg : 0 ≤ C * (Dbar * a) := mul_nonneg hC (mul_nonneg hD0 ha)
      have hraw :
          ENNReal.ofReal (Cbar * C * a) ^ r ≤
            (ENNReal.ofReal C) ^ r * ENNReal.ofReal (Dbar * a) ^ r := by
          calc
            _ ≤ ENNReal.ofReal (C * (Dbar * a)) ^ r :=
              pow_le_pow_left' (ENNReal.ofReal_le_ofReal hmul) r
            _ = _ := by rw [ENNReal.ofReal_mul hC, mul_pow]
      convert hraw using 1 <;> dsimp [a] <;> simp only [mul_assoc]
    calc
      _ ≤ (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
          ((ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r +
            ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
              ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
                ((ENNReal.ofReal C) ^ r *
                  ENNReal.ofReal (Dbar *
                    24 ^ (𝒯.deg i - 𝒯.deg k +
                      (if (i, k) ∈ D then 0 else κ)) *
                    4 ^ (𝒯.deg k - 𝒯.deg j +
                      (if (k, j) ∈ D then 0 else κ))) ^ r)) := by
        have hsum' := Finset.sum_le_sum hsum
        exact mul_le_mul_of_nonneg_left
          (add_le_add hfirst
            (mul_le_mul_of_nonneg_left hsum' (by positivity)))
          (by positivity)
      _ = (ENNReal.ofReal C) ^ r *
          gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r := by
        dsimp [gammaSplitLeftConstant]
        rw [← Finset.mul_sum]
        simp only [one_mul, mul_one]
        ring
  have hright : gammaSplitRightConstant 𝒯 D i j κ C Cbar r ≤
      (ENNReal.ofReal C) ^ r *
        gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r := by
    dsimp [gammaSplitRightConstant]
    have hfirst :
        (ENNReal.ofReal (C * 4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r) ≤
          (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r := by
      rw [ENNReal.ofReal_mul hC, mul_pow]
    have hsum : ∀ k ∈ gammaGoodIntermediate 𝒯 D i j,
        ENNReal.ofReal (Cbar * C *
            4 ^ (𝒯.deg i - 𝒯.deg k +
              (if (i, k) ∈ D then 0 else κ)) *
            24 ^ (𝒯.deg k - 𝒯.deg j +
              (if (k, j) ∈ D then 0 else κ))) ^ r ≤
          (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (Dbar *
              4 ^ (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
              24 ^ (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ r := by
      intro k hk
      let a : ℝ := 4 ^ (𝒯.deg i - 𝒯.deg k +
          (if (i, k) ∈ D then 0 else κ)) *
        24 ^ (𝒯.deg k - 𝒯.deg j +
          (if (k, j) ∈ D then 0 else κ))
      have ha : 0 ≤ a := by
        dsimp [a]
        positivity
      have hmul : Cbar * C * a ≤ C * (Dbar * a) := by
        calc
          Cbar * C * a = C * (Cbar * a) := by ring
          _ ≤ C * (Dbar * a) := by
            gcongr
            exact show Cbar ≤ Dbar by dsimp [Dbar]; exact le_max_right _ _
      have hraw :
          ENNReal.ofReal (Cbar * C * a) ^ r ≤
            (ENNReal.ofReal C) ^ r * ENNReal.ofReal (Dbar * a) ^ r := by
          calc
            _ ≤ ENNReal.ofReal (C * (Dbar * a)) ^ r :=
              pow_le_pow_left' (ENNReal.ofReal_le_ofReal hmul) r
            _ = _ := by rw [ENNReal.ofReal_mul hC, mul_pow]
      convert hraw using 1 <;> dsimp [a] <;> simp only [mul_assoc]
    calc
      _ ≤ (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
          ((ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (4 ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ r +
            ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
              ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
                ((ENNReal.ofReal C) ^ r *
                  ENNReal.ofReal (Dbar *
                    4 ^ (𝒯.deg i - 𝒯.deg k +
                      (if (i, k) ∈ D then 0 else κ)) *
                    24 ^ (𝒯.deg k - 𝒯.deg j +
                      (if (k, j) ∈ D then 0 else κ))) ^ r)) := by
        have hsum' := Finset.sum_le_sum hsum
        exact mul_le_mul_of_nonneg_left
          (add_le_add hfirst
            (mul_le_mul_of_nonneg_left hsum' (by positivity)))
          (by positivity)
      _ = (ENNReal.ofReal C) ^ r *
          gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r := by
        dsimp [gammaSplitRightConstant]
        rw [← Finset.mul_sum]
        simp only [one_mul, mul_one]
        ring
  have hglobal : gammaSplitGlobalConstant 𝒯 D i j κ C Cbar δ r ≤
      (ENNReal.ofReal C) ^ r *
        gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r := by
    dsimp [gammaSplitGlobalConstant]
    calc
      _ ≤ ((2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
          ((ENNReal.ofReal C) ^ r *
            (gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
              gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r))) *
          (1 - ((2 : ℝ≥0∞)⁻¹) ^
            (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹ *
          (1 - ((2 : ℝ≥0∞)⁻¹) ^
            (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹ := by
        have hadd :
            gammaSplitLeftConstant 𝒯 D i j κ C Cbar r +
                gammaSplitRightConstant 𝒯 D i j κ C Cbar r ≤
              (ENNReal.ofReal C) ^ r *
                (gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
                  gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r) := by
          calc
            _ ≤ (ENNReal.ofReal C) ^ r *
                gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
                (ENNReal.ofReal C) ^ r *
                  gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r :=
              add_le_add hleft hright
            _ = _ := by ring
        let d₀ : ℝ≥0∞ :=
          (1 - ((2 : ℝ≥0∞)⁻¹) ^
            (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹
        let A₀ : ℝ≥0∞ :=
          (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2
        have hscaled : A₀ *
              (gammaSplitLeftConstant 𝒯 D i j κ C Cbar r +
                gammaSplitRightConstant 𝒯 D i j κ C Cbar r) ≤
            A₀ * ((ENNReal.ofReal C) ^ r *
              (gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
                gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r)) := by
          exact mul_le_mul_of_nonneg_left hadd (by positivity)
        have hprod :
            ((2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
              (gammaSplitLeftConstant 𝒯 D i j κ C Cbar r +
                gammaSplitRightConstant 𝒯 D i j κ C Cbar r)) * d₀ * d₀ ≤
            ((2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
              ((ENNReal.ofReal C) ^ r *
                (gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
                  gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r))) * d₀ * d₀ := by
          calc
            _ = (A₀ *
                (gammaSplitLeftConstant 𝒯 D i j κ C Cbar r +
                  gammaSplitRightConstant 𝒯 D i j κ C Cbar r)) * d₀ * d₀ := by
              dsimp [A₀]
            _ ≤ (A₀ * ((ENNReal.ofReal C) ^ r *
                (gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r +
                  gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r))) * d₀ * d₀ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hscaled (by positivity)) (by positivity)
            _ = _ := by
              dsimp [A₀]
        simpa [d₀, mul_assoc, mul_left_comm, mul_comm] using hprod
      _ = _ := by ring
  have hbad : gammaSplitBadConstant 𝒯 D i j C r ≤
      ENNReal.ofReal C * ENNReal.ofReal Dbar *
        gammaSplitBadConstant 𝒯 D i j 1 r := by
    dsimp [gammaSplitBadConstant]
    rw [mul_add]
    apply add_le_add
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      let a : ℝ := 24 ^ (𝒯.deg i - 𝒯.deg k) * 4 ^ (𝒯.deg k - 𝒯.deg j)
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hmul : C ^ 2 * a ≤ C * (Dbar * a) := by
        calc
          C ^ 2 * a = C * (C * a) := by rw [pow_two, mul_assoc]
          _ ≤ C * (Dbar * a) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hCD ha) hC
      have hmul' : C ^ 2 *
          24 ^ (𝒯.deg i - 𝒯.deg k) * 4 ^ (𝒯.deg k - 𝒯.deg j) ≤
          C * (Dbar * a) := by simpa [a, mul_assoc] using hmul
      calc
        _ ≤ ENNReal.ofReal (C * (Dbar * a)) :=
          ENNReal.ofReal_le_ofReal hmul'
        _ = ENNReal.ofReal C * ENNReal.ofReal Dbar *
            ENNReal.ofReal (1 ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hD0]
          simp [a, Dbar, mul_assoc]
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      let a : ℝ := 24 ^ (𝒯.deg k - 𝒯.deg j) * 4 ^ (𝒯.deg i - 𝒯.deg k)
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hmul : C ^ 2 * a ≤ C * (Dbar * a) := by
        calc
          C ^ 2 * a = C * (C * a) := by rw [pow_two, mul_assoc]
          _ ≤ C * (Dbar * a) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hCD ha) hC
      have hmul' : C ^ 2 *
          24 ^ (𝒯.deg k - 𝒯.deg j) * 4 ^ (𝒯.deg i - 𝒯.deg k) ≤
          C * (Dbar * a) := by simpa [a, mul_assoc] using hmul
      calc
        _ ≤ ENNReal.ofReal (C * (Dbar * a)) :=
          ENNReal.ofReal_le_ofReal hmul'
        _ = ENNReal.ofReal C * ENNReal.ofReal Dbar *
            ENNReal.ofReal (1 ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hD0]
          simp [a, Dbar, mul_assoc]
  have hbadpow : gammaSplitBadConstant 𝒯 D i j C r ^ r ≤
      (ENNReal.ofReal C) ^ r * (ENNReal.ofReal Dbar) ^ r *
        gammaSplitBadConstant 𝒯 D i j 1 r ^ r := by
    calc
      _ ≤ (ENNReal.ofReal C * ENNReal.ofReal Dbar *
          gammaSplitBadConstant 𝒯 D i j 1 r) ^ r := by
        exact pow_le_pow_left' hbad r
      _ = _ := by rw [mul_pow, mul_pow]
  dsimp [gammaSplitUnitConstant, gammaSplitUnitProfile]
  have hinner :
      gammaSplitCellConstant 𝒯 i j κ C r +
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
            gammaSplitGlobalConstant 𝒯 D i j κ C Cbar δ r +
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
            gammaSplitBadConstant 𝒯 D i j C r ^ r ≤
        (ENNReal.ofReal C) ^ r *
          (gammaSplitCellConstant 𝒯 i j κ 1 r +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
              gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
              (ENNReal.ofReal Dbar) ^ r *
                gammaSplitBadConstant 𝒯 D i j 1 r ^ r) := by
    calc
      _ ≤ (ENNReal.ofReal C) ^ r *
          gammaSplitCellConstant 𝒯 i j κ 1 r +
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
            ((ENNReal.ofReal C) ^ r *
              gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r) +
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
            ((ENNReal.ofReal C) ^ r * (ENNReal.ofReal Dbar) ^ r *
              gammaSplitBadConstant 𝒯 D i j 1 r ^ r) := by
        have hglobal' :
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                gammaSplitGlobalConstant 𝒯 D i j κ C Cbar δ r ≤
              (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                ((ENNReal.ofReal C) ^ r *
                  gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r) :=
          mul_le_mul_of_nonneg_left hglobal (by positivity)
        have hbadpow' :
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                gammaSplitBadConstant 𝒯 D i j C r ^ r ≤
              (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                ((ENNReal.ofReal C) ^ r * (ENNReal.ofReal Dbar) ^ r *
                  gammaSplitBadConstant 𝒯 D i j 1 r ^ r) :=
          mul_le_mul_of_nonneg_left hbadpow (by positivity)
        calc
          _ ≤ (ENNReal.ofReal C) ^ r *
              gammaSplitCellConstant 𝒯 i j κ 1 r +
              (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                ((ENNReal.ofReal C) ^ r *
                  gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r) +
              (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
                ((ENNReal.ofReal C) ^ r * (ENNReal.ofReal Dbar) ^ r *
                  gammaSplitBadConstant 𝒯 D i j 1 r ^ r) := by
            exact add_le_add (add_le_add hcell.le hglobal') hbadpow'
          _ = _ := by ring
      _ = _ := by ring
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ (𝒯.deg i - 𝒯.deg j)) ^ r *
        (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        ((ENNReal.ofReal C) ^ r *
          (gammaSplitCellConstant 𝒯 i j κ 1 r +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
              gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r *
              (ENNReal.ofReal Dbar) ^ r *
                gammaSplitBadConstant 𝒯 D i j 1 r ^ r)) := by
          exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by ring

end RegularityStructures

end
