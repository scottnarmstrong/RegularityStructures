/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Shell

/-!
# Smoothness and support of the annihilating kernel

Smoothness and support of `annBump` and `annKernel0`, and the moments of `annBump`.

Source: [Hai14, Lemma 5.5].
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem contDiff_annBump (N : ℕ) : ContDiff ℝ ∞ (annBump N) :=
  (Classical.choose_spec (exists_annBump N)).1

theorem annBump_eq_zero {N : ℕ} {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annBump N z = 0 :=
  (Classical.choose_spec (exists_annBump N)).2.1 z hz

theorem integral_monomial_mul_annBump {N : ℕ} (k : PolyIndex N) :
    ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * annBump N z = annMoment k :=
  (Classical.choose_spec (exists_annBump N)).2.2 k

theorem contDiff_annKernel0 (N : ℕ) : ContDiff ℝ ∞ (annKernel0 N) := by
  unfold annKernel0
  exact ((contDiff_heatShell 0).sub (contDiff_annBump N)).add
    (contDiff_const.mul ((contDiff_annBump N).comp (parabolicDilateCLM 2).contDiff))

theorem annKernel0_eq_zero (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annKernel0 N z = 0 := by
  have h1 : heatShell 0 z = 0 := heatShell_eq_zero (by simpa using hz)
  have h2 : 1 < parabolicNorm (parabolicDilate 2 z) := by
    rw [parabolicNorm_parabolicDilate (by norm_num)]
    linarith [parabolicNorm_nonneg z]
  simp [annKernel0, h1, annBump_eq_zero hz, annBump_eq_zero h2]

end RegularityStructures

end
