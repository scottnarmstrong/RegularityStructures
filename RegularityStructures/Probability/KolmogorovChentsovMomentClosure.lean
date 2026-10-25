/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovGrid
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Normalised dyadic moments

This file normalises the close-pair supremum by the Hölder scale.  The five
neighbours at each level give a purely geometric series, so the strict
condition `p * r < q - 1` is visible directly in the ratio.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
  {P : Measure Ω}

noncomputable def dyadicNormalised (X : UnitInterval → Ω → E) (r : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  dyadicCloseSup X n ω * (dyadicBase n) ^ (-(r : ℝ))

theorem ofReal_four_div_two_pow (n : ℕ) :
    ENNReal.ofReal (4 / (2 : ℝ) ^ n) =
      (4 : ℝ≥0∞) * dyadicBase n := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.inv_pow]
  norm_num [dyadicBase]

theorem dyadicCloseSup_aemeasurable (X : UnitInterval → Ω → E)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (n : ℕ) : AEMeasurable (dyadicCloseSup X n) P := by
  unfold dyadicCloseSup
  apply AEMeasurable.iSup
  intro i
  apply AEMeasurable.iSup
  intro d
  exact hmeas _ _

theorem dyadicNormalised_lintegral_pow_le {p : ℕ} {q : ℝ} {M : ℝ≥0∞}
    {r : ℝ≥0} (hp : 1 ≤ p) (hq : 0 ≤ q) (_hr : 0 ≤ r)
    (_hpr : (p : ℝ) * (r : ℝ) < q - 1)
    (X : UnitInterval → Ω → E)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
      M * edist s t ^ q) (n : ℕ) :
    ∫⁻ ω, dyadicNormalised X r n ω ^ p ∂P ≤
      (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
        (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
  have hp0 : p ≠ 0 := by omega
  have hZ := dyadicCloseSup_lintegral_pow_le hp hq X hmeas hpair n
  have hZm := dyadicCloseSup_aemeasurable X hmeas n
  have hbase : dyadicBase n ≠ 0 := (dyadicBase_pos n).ne'
  have hbase_top : dyadicBase n ≠ ∞ := dyadicBase_ne_top n
  have hpow : ∀ z : ℝ≥0∞,
      (z * (dyadicBase n) ^ (-(r : ℝ))) ^ p =
        z ^ p * (dyadicBase n) ^ (-(r : ℝ) * p) := by
    intro z
    have hbasepow : ((dyadicBase n) ^ (-(r : ℝ))) ^ p =
        (dyadicBase n) ^ (-(r : ℝ) * (p : ℝ)) := by
      calc
        ((dyadicBase n) ^ (-(r : ℝ))) ^ p =
            ((dyadicBase n) ^ (-(r : ℝ))) ^ (p : ℝ) :=
          (ENNReal.rpow_natCast _ p).symm
        _ = (dyadicBase n) ^ (-(r : ℝ) * (p : ℝ)) :=
          (ENNReal.rpow_mul _ _ _).symm
    rw [mul_pow, hbasepow]
  calc
    ∫⁻ ω, dyadicNormalised X r n ω ^ p ∂P =
        (∫⁻ ω, dyadicCloseSup X n ω ^ p ∂P) *
          (dyadicBase n) ^ (-(r : ℝ) * p) := by
      unfold dyadicNormalised
      simp_rw [hpow]
      rw [lintegral_mul_const'' _ (hZm.pow_const p)]
    _ ≤ (((2 ^ n + 1 : ℕ) : ℝ≥0∞) * 5 *
          (M * (ENNReal.ofReal (4 / (2 : ℝ) ^ n)) ^ q)) *
          (dyadicBase n) ^ (-(r : ℝ) * p) := by
      gcongr
    _ = (((2 : ℝ≥0∞) ^ n + 1) * 5 *
          (M * ((4 : ℝ≥0∞) * dyadicBase n) ^ q)) *
          (dyadicBase n) ^ (-(r : ℝ) * p) := by
      rw [ofReal_four_div_two_pow n]
      norm_num
    _ ≤ (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
          (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
      have hcard : (2 : ℝ≥0∞) ^ n + 1 ≤ (2 : ℝ≥0∞) ^ (n + 1) := by
        rw [pow_succ]
        have hone : (1 : ℝ≥0∞) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        calc
          (2 : ℝ≥0∞) ^ n + 1 = 1 + (2 : ℝ≥0∞) ^ n := by ac_rfl
          _ ≤ (2 : ℝ≥0∞) ^ n + (2 : ℝ≥0∞) ^ n := add_le_add_left hone _
          _ = (2 : ℝ≥0∞) ^ n * 2 := by ring
      have hbasepow : (2 : ℝ≥0∞) ^ n * dyadicBase n = 1 := by
        rw [dyadicBase, ← mul_pow]
        rw [ENNReal.mul_inv_cancel] <;> norm_num
      calc
        (((2 : ℝ≥0∞) ^ n + 1) * 5 *
            (M * ((4 : ℝ≥0∞) * dyadicBase n) ^ q)) *
            (dyadicBase n) ^ (-(r : ℝ) * p) ≤
            ((2 : ℝ≥0∞) ^ (n + 1) * 5 *
              (M * ((4 : ℝ≥0∞) * dyadicBase n) ^ q)) *
              (dyadicBase n) ^ (-(r : ℝ) * p) := by
          gcongr
        _ = (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
            (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
          calc
            2 ^ (n + 1) * 5 * (M * (4 ^ q * dyadicBase n ^ q)) *
                dyadicBase n ^ (-(r : ℝ) * p) =
                2 ^ (n + 1) * 5 * M * 4 ^ q *
                  (dyadicBase n ^ q * dyadicBase n ^ (-(r : ℝ) * p)) := by ring
            _ = 2 ^ (n + 1) * 5 * M * 4 ^ q *
                  dyadicBase n ^ (q - (p : ℝ) * (r : ℝ)) := by
              rw [← ENNReal.rpow_add _ _ hbase hbase_top]
              congr 4
              ring
            _ = 10 * M * 4 ^ q *
                  (2 ^ n * dyadicBase n ^
                    (q - (p : ℝ) * (r : ℝ))) := by
              rw [pow_succ]
              ring
            _ = 10 * M * 4 ^ q *
                  (2 ^ n * (dyadicBase n ^
                    (q - (p : ℝ) * (r : ℝ) - 1) * dyadicBase n)) := by
              have hpowdelta : dyadicBase n ^
                    (q - (p : ℝ) * (r : ℝ)) =
                    dyadicBase n ^ (q - (p : ℝ) * (r : ℝ) - 1) *
                      dyadicBase n := by
                calc
                  dyadicBase n ^ (q - (p : ℝ) * (r : ℝ)) =
                      dyadicBase n ^
                        ((q - (p : ℝ) * (r : ℝ) - 1) + 1) := by
                    congr 1
                    ring
                  _ = dyadicBase n ^ (q - (p : ℝ) * (r : ℝ) - 1) *
                      dyadicBase n := by
                    rw [ENNReal.rpow_add _ _ hbase hbase_top,
                      ENNReal.rpow_one]
              rw [hpowdelta]
            _ = 10 * M * 4 ^ q *
                  dyadicBase n ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
              calc
                10 * M * 4 ^ q *
                    (2 ^ n * (dyadicBase n ^
                      (q - (p : ℝ) * (r : ℝ) - 1) * dyadicBase n)) =
                    10 * M * 4 ^ q *
                      ((2 ^ n * dyadicBase n) *
                        dyadicBase n ^ (q - (p : ℝ) * (r : ℝ) - 1)) := by
                        ac_rfl
                _ = 10 * M * 4 ^ q *
                      dyadicBase n ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
                  rw [hbasepow, one_mul]

end RegularityStructures

end
