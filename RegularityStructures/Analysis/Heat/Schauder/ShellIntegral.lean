/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Shell
public import RegularityStructures.Analysis.Heat.Decomposition
public import RegularityStructures.Analysis.Heat.Schauder.Reflect
public import RegularityStructures.Analysis.Heat.Schauder.ReflectPairing
public import RegularityStructures.Analysis.Heat.Decomposition.MomentDegree

/-!
# `L¹` norms of the heat shells

The heat shells as rescalings (`heatShell_eq_mul_rescaled`) and their `L¹` norms and those of their
generator images (`integral_abs_heatShell`, `integral_abs_parabolicGenerator_heatShell`).

Source: [Hai14, Lemma 5.5].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem heatShell_eq_mul_rescaled (n : ℕ) (w : ParabolicSpace) :
    heatShell n w = ((2 : ℝ) ^ n)⁻¹ ^ 2 *
      rescaledTestFunction (heatShell 0) (((2 : ℝ) ^ n)⁻¹) 0 w := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  rw [heatShell_eq_scale n w]
  simp only [rescaledTestFunction, sub_zero, inv_inv]
  field_simp

theorem integral_abs_heatShell (n : ℕ) :
    ∫ w, |heatShell n w| = ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |heatShell 0 w| := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have e : ∀ w, |heatShell n w| = ((2 : ℝ) ^ n)⁻¹ ^ 2 *
      rescaledTestFunction (fun u => |heatShell 0 u|) (((2 : ℝ) ^ n)⁻¹) 0 w := by
    intro w
    rw [heatShell_eq_mul_rescaled, abs_mul, abs_of_pos (by positivity)]
    unfold rescaledTestFunction
    rw [abs_mul, abs_of_pos (by positivity)]
  simp_rw [e]
  rw [integral_const_mul, integral_rescaledTestFunction _ (inv_pos.2 h2)]

theorem integral_abs_parabolicGenerator_heatShell (n : ℕ) :
    ∫ w, |parabolicGenerator (heatShell n) w| =
      ((2 : ℝ) ^ n) ^ 2 * ∫ w, |parabolicGenerator (heatShell 0) w| := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hc : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.2 h2
  have hfun : heatShell n = fun w => ((2 : ℝ) ^ n)⁻¹ ^ 2 *
      rescaledTestFunction (heatShell 0) (((2 : ℝ) ^ n)⁻¹) 0 w := funext (heatShell_eq_mul_rescaled n)
  have hsm := contDiff_rescaledTestFunction (contDiff_heatShell 0) (((2 : ℝ) ^ n)⁻¹) 0
  have e : ∀ w, |parabolicGenerator (heatShell n) w| = ((2 : ℝ) ^ n) ^ 2 *
      rescaledTestFunction (fun u => |parabolicGenerator (heatShell 0) u|)
        (((2 : ℝ) ^ n)⁻¹) 0 w := by
    intro w
    rw [hfun, parabolicGenerator_const_mul hsm]
    beta_reduce
    rw [parabolicGenerator_rescaledTestFunction (contDiff_heatShell 0) hc]
    unfold rescaledTestFunction
    simp only [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (((2 : ℝ) ^ n)⁻¹ ^ 5)⁻¹),
      abs_of_pos (by positivity : (0 : ℝ) < (((2 : ℝ) ^ n)⁻¹ ^ 4)⁻¹),
      abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ ^ 2)]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_rescaledTestFunction _ hc]

end RegularityStructures

end
