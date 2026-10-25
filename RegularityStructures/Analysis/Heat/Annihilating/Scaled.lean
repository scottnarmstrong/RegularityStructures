/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition

/-!
# Dyadic rescalings of a bump

For `h : ℝ⁴ → ℝ` we set `scaledShell h n z = (2^n)^3 h(S^{2^n} z)` (`S^c = parabolicDilate c`).
If `h` is smooth and supported in the unit parabolic ball, then `scaledShell h n` is smooth and
supported in `‖z‖_𝔰 ≤ 2^{-n}`, its derivatives obey the exact scaling
`D_J (scaledShell h n) = (2^n)^{3 + |J|_𝔰} (D_J h)(S^{2^n} ·)`, and its moments scale exactly.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The `n`-th dyadic rescaling `z ↦ (2^n)^3 h(S^{2^n} z)` of `h`. -/
def scaledShell (h : ParabolicSpace → ℝ) (n : ℕ) (z : ParabolicSpace) : ℝ :=
  ((2 : ℝ) ^ n) ^ 3 * h (parabolicDilate (2 ^ n) z)

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem scaledShell_eq_smul_comp (h : ParabolicSpace → ℝ) (n : ℕ) :
    scaledShell h n = ((2 : ℝ) ^ n) ^ 3 • (h ∘ parabolicDilateCLM (2 ^ n)) := by
  funext z
  simp [scaledShell]

theorem contDiff_scaledShell {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (scaledShell h n) := by
  rw [scaledShell_eq_smul_comp]
  exact (hh.comp (parabolicDilateCLM (2 ^ n)).contDiff).const_smul (((2 : ℝ) ^ n) ^ 3)

theorem scaledShell_eq_zero {h : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) {n : ℕ} {z : ParabolicSpace}
    (hz : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) : scaledShell h n z = 0 := by
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have : 1 < parabolicNorm (parabolicDilate (2 ^ n) z) := by
    rw [parabolicNorm_parabolicDilate hc.le]
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ hc] at hz
    linarith
  simp [scaledShell, hs _ this]

theorem hasCompactSupport_scaledShell {h : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (n : ℕ) : HasCompactSupport (scaledShell h n) :=
  HasCompactSupport.intro (isCompact_parabolicNorm_le ((2 : ℝ)⁻¹ ^ n)) fun _ hz =>
    scaledShell_eq_zero hs (not_le.1 hz)

/-- Derivative scaling: the `J`-derivative of the `n`-th rescaling is that of `h` at the dilated
point, times `(2^n)^{3 + |J|_𝔰}`. -/
theorem lineIter_coordDir_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (n : ℕ)
    (J : List (Fin 4)) (z : ParabolicSpace) :
    lineIter (J.map coordDir) (scaledShell h n) z =
      ((2 : ℝ) ^ n) ^ (3 + indexWeight J) *
        lineIter (J.map coordDir) h (parabolicDilate (2 ^ n) z) := by
  have hA : ContDiff ℝ ∞ (h ∘ parabolicDilateCLM (2 ^ n)) :=
    h0.comp (parabolicDilateCLM (2 ^ n)).contDiff
  rw [scaledShell_eq_smul_comp, lineIter_const_smul hA, lineIter_comp_clm h0]
  have hmap : (J.map coordDir).map (parabolicDilateCLM ((2 : ℝ) ^ n)) =
      J.map fun j => ((2 : ℝ) ^ n) ^ parabolicWeight j • coordDir j := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => parabolicDilateCLM_coordDir _ j
  rw [hmap, lineIter_map_smul h0 (fun j => ((2 : ℝ) ^ n) ^ parabolicWeight j) coordDir J,
    prod_map_pow]
  simp [pow_add, mul_assoc]

end RegularityStructures

end
