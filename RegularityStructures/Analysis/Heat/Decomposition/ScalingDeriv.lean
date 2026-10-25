/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Heat.Decomposition.SupportBound
public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Analysis.Parabolic.RegularisingDecomposition

/-!
# Scaling of the derivatives of the heat shells

The `J`-derivative of the `n`-th heat shell is that of the zeroth shell at the dilated point, times
`(2^n)^{3 + |J|_𝔰}` (`lineIter_coordDir_heatShell`); mixed derivatives of a function of `x - y`
(`kernelDeriv_sub`).

Source: [Hai14, Lemma 5.5].
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem count_toList (k : Fin 4 →₀ ℕ) (i : Fin 4) :
    (Finsupp.toMultiset k).toList.count i = k i := by
  rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]

theorem heatShell_eq_smul_comp (n : ℕ) :
    heatShell n = ((2 : ℝ) ^ n) ^ 3 • (heatShell 0 ∘ parabolicDilateCLM (2 ^ n)) := by
  funext z
  simp [heatShell_eq_scale n z]

/-- Derivative scaling: the `J`-derivative of the `n`-th shell is that of the zeroth shell at the
dilated point, times `(2^n)^{3 + |J|_𝔰}`. -/
theorem lineIter_coordDir_heatShell (n : ℕ) (J : List (Fin 4)) (z : ParabolicSpace) :
    lineIter (J.map coordDir) (heatShell n) z =
      ((2 : ℝ) ^ n) ^ (3 + indexWeight J) *
        lineIter (J.map coordDir) (heatShell 0) (parabolicDilate (2 ^ n) z) := by
  have h0 := contDiff_heatShell 0
  have hA : ContDiff ℝ ∞ (heatShell 0 ∘ parabolicDilateCLM (2 ^ n)) :=
    h0.comp (parabolicDilateCLM (2 ^ n)).contDiff
  rw [heatShell_eq_smul_comp, lineIter_const_smul hA, lineIter_comp_clm h0]
  have hmap : (J.map coordDir).map (parabolicDilateCLM ((2 : ℝ) ^ n)) =
      J.map fun j => ((2 : ℝ) ^ n) ^ parabolicWeight j • coordDir j := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => parabolicDilateCLM_coordDir _ j
  rw [hmap, lineIter_map_smul h0 (fun j => ((2 : ℝ) ^ n) ^ parabolicWeight j) coordDir J,
    prod_map_pow]
  simp [pow_add, mul_assoc]

/-- Mixed derivatives of a function of `x - y` are derivatives of the function, up to the sign
`(-1)^{|l|}`. -/
theorem kernelDeriv_sub {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) (k l : Fin 4 →₀ ℕ)
    (x y : ParabolicSpace) :
    kernelDeriv k l (fun x y => h (x - y)) x y =
      (-1 : ℝ) ^ (multiDirs l).length * lineIter (multiDirs k ++ multiDirs l) h (x - y) := by
  set S : ParabolicSpace × ParabolicSpace →L[ℝ] ParabolicSpace :=
    ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _ with hS
  have hF : Function.uncurry (fun x y : ParabolicSpace => h (x - y)) = h ∘ S := by
    funext p; simp [hS, Function.uncurry]
  have hsm : ContDiff ℝ ∞ (h ∘ S) := hh.comp S.contDiff
  unfold kernelDeriv
  simp only
  have := congrFun (iteratedFDeriv_get_eq_lineIter hsm
    ((multiDirs k).map (fun v => (v, (0 : ParabolicSpace))) ++
      (multiDirs l).map (fun v => ((0 : ParabolicSpace), v)))) (x, y)
  rw [hF]
  refine this.trans ?_
  rw [lineIter_comp_clm hh S, Function.comp_apply, List.map_append]
  simp only [List.map_map, Function.comp_def, hS, sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', sub_zero, zero_sub,
    List.map_id']
  rw [lineIter_append, show (multiDirs l).map (fun v => -v) = (multiDirs l).map Neg.neg from rfl,
    lineIter_map_neg hh, lineIter_const_smul (contDiff_lineIter hh _), lineIter_append]
  simp

end RegularityStructures

end
