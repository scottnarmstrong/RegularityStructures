/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# Vanishing monomial moments of the modified shells

`∫ z^k annShell N n z dz = 0` for all `n` and every multi-index `k` with `|k|_𝔰 < N`
(`integral_monomial_mul_annShell`): the moments of `annShell N n` are those of
`annKernel0 N`, rescaled by `2^{-(2 + |k|_𝔰) n}`, and the choice of `ψ` makes the moments of
`annKernel0 N` vanish.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5 (Assumption 5.4).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem integral_monoFn_mul_scaledShell (h : ParabolicSpace → ℝ) (l : Fin 4 →₀ ℕ) (n : ℕ) :
    ∫ z, monoFn l z * scaledShell h n z =
      ((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ multiDeg l)⁻¹ * (((2 : ℝ) ^ n) ^ 5)⁻¹ *
        ∫ z, monoFn l z * h z := by
  have hd : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hpt : ∀ z, monoFn l z * scaledShell h n z =
      (((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ multiDeg l)⁻¹) *
        ((fun w => monoFn l w * h w) (parabolicDilate (2 ^ n) z)) := by
    intro z
    simp only [scaledShell, monoFn_parabolicDilate]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_parabolicDilate (fun w => monoFn l w * h w) hd]
  ring

theorem integrable_monoFn_mul {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (l : Fin 4 →₀ ℕ) :
    Integrable fun z => monoFn l z * h z := by
  have hcs : HasCompactSupport h :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun _ hz => hs _ (not_le.1 hz)
  exact ((contDiff_monoFn l).continuous.mul h0.continuous).integrable_of_hasCompactSupport
    hcs.mul_left

end RegularityStructures

end
