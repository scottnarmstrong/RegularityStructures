/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorSum
public import RegularityStructures.Analysis.Heat.Schauder.Diff
public import RegularityStructures.Analysis.Heat.Schauder.TaylorGen

/-!
# Scaling of derivative words of the dyadic pieces

For a word `ℓ : List (Fin 4)` of coordinate directions, `D^ℓ (scaledShell h n)` is
`(2^n)^{|ℓ|_𝔰}` times `scaledShell (D^ℓ h) n`, and the `L¹` norms of `D^ℓ (scaledShell h n)` and of
`L D^ℓ (scaledShell h n)` scale as `(2^n)^{|ℓ|_𝔰 - 2}` and `(2^n)^{|ℓ|_𝔰 + 2}`
(`integral_abs_word_scaledShell`, `integral_abs_gen_word_scaledShell`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem lineIter_word_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (ℓ : List (Fin 4)) (n : ℕ) :
    lineIter (ℓ.map coordDir) (scaledShell h n) =
      fun w => ((2 : ℝ) ^ n) ^ indexWeight ℓ * scaledShell (lineIter (ℓ.map coordDir) h) n w := by
  funext w
  rw [lineIter_coordDir_scaledShell h0 n ℓ w]
  simp only [scaledShell, pow_add]
  ring

theorem parabolicGenerator_lineIter {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (K : List ParabolicSpace) :
    parabolicGenerator (lineIter K f) = lineIter K (parabolicGenerator f) := by
  induction K with
  | nil => rfl
  | cons d K ih =>
    rw [lineIter_cons, lineIter_cons, ← ih]
    exact parabolicGenerator_dirDeriv (contDiff_lineIter hf K) d

theorem integral_abs_word_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (ℓ : List (Fin 4)) (n : ℕ) :
    ∫ w, |lineIter (ℓ.map coordDir) (scaledShell h n) w| =
      ((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n)⁻¹ ^ 2 *
        ∫ w, |lineIter (ℓ.map coordDir) h w|) := by
  have hN : (0 : ℝ) < ((2 : ℝ) ^ n) ^ indexWeight ℓ := by positivity
  rw [lineIter_word_scaledShell h0]
  have : ∀ w, |((2 : ℝ) ^ n) ^ indexWeight ℓ * scaledShell (lineIter (ℓ.map coordDir) h) n w| =
      ((2 : ℝ) ^ n) ^ indexWeight ℓ * |scaledShell (lineIter (ℓ.map coordDir) h) n w| :=
    fun w => by rw [abs_mul, abs_of_pos hN]
  simp_rw [this]
  rw [integral_const_mul, integral_abs_scaledShell]

theorem parabolicGenerator_scaledShell_eq {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    parabolicGenerator (scaledShell F n) =
      fun w => ((2 : ℝ) ^ n) ^ 4 * scaledShell (parabolicGenerator F) n w := by
  funext w
  rw [parabolicGenerator_scaledShell hF]
  simp only [scaledShell]
  ring

theorem integral_abs_gen_word_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (ℓ : List (Fin 4)) (n : ℕ) :
    ∫ w, |parabolicGenerator (lineIter (ℓ.map coordDir) (scaledShell h n)) w| =
      ((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 *
        ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w|) := by
  have hN : (0 : ℝ) < ((2 : ℝ) ^ n) := pow_pos (by norm_num) n
  have hLh := contDiff_parabolicGenerator h0
  rw [parabolicGenerator_lineIter (contDiff_scaledShell h0 n), parabolicGenerator_scaledShell_eq h0,
    lineIter_const_mul (contDiff_scaledShell hLh n), lineIter_word_scaledShell hLh]
  have : ∀ w, |((2 : ℝ) ^ n) ^ 4 * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
      scaledShell (lineIter (ℓ.map coordDir) (parabolicGenerator h)) n w)| =
      ((2 : ℝ) ^ n) ^ 4 * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
        |scaledShell (lineIter (ℓ.map coordDir) (parabolicGenerator h)) n w|) := by
    intro w
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 4),
      abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n) ^ indexWeight ℓ)]
  simp_rw [this]
  rw [integral_const_mul, integral_const_mul, integral_abs_scaledShell]
  field_simp

end RegularityStructures

end
