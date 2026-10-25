/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothGrowth
public import Phi43.Structure.CanonicalModel
import Mathlib.Tactic.FinCases

/-!+# Smoothness and growth of the canonical basis functions

The concrete, actual-kernel functions in Hairer [Hai14, (8.24)--(8.25)]
are smooth and polynomially bounded when the smooth noise is polynomially
bounded. These are function estimates, not hypotheses on an abstract model.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem coord_bound (i : Fin 4) (z : ParabolicSpace) :
    |parabolicCoords z i| ≤ (1 + parabolicNorm z) ^ 2 := by
  have hn := parabolicNorm_nonneg z
  have hs : Real.sqrt |z.1| ≤ parabolicNorm z := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have ht : |z.1| ≤ (1 + parabolicNorm z) ^ 2 := by
    nlinarith [Real.sq_sqrt (abs_nonneg z.1), Real.sqrt_nonneg |z.1|]
  have hx (j : Fin 3) : |z.2 j| ≤ (1 + parabolicNorm z) ^ 2 := by
    have hj := Finset.single_le_sum (f := fun j : Fin 3 => |z.2 j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have : |z.2 j| ≤ parabolicNorm z := by
      unfold parabolicNorm
      linarith [Real.sqrt_nonneg |z.1|]
    nlinarith
  fin_cases i <;> first | exact ht | exact hx _

open scoped ContDiff in
private theorem coord_smooth (i : Fin 4) :
    ContDiff ℝ ∞ (fun z : ParabolicSpace => parabolicCoords z i) := by
  fin_cases i
  · exact contDiff_fst
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : ParabolicSpace => z.2 2)
    fun_prop

private theorem coord_growth (i : Fin 4) :
    PolyBounded (fun z : ParabolicSpace => parabolicCoords z i) :=
  ⟨(coord_smooth i).continuous.measurable, 1, 2, fun z => by simpa using coord_bound i z⟩

private theorem one_growth : PolyBounded (fun _ : ParabolicSpace => (1 : ℝ)) :=
  ⟨measurable_const, 1, 0, fun _ => by simp⟩

open scoped ContDiff in
/-- Every unbased symbol has a smooth actual-kernel realisation. -/
theorem canonicalGlobalPiBasis_smooth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (τ : Symbol) :
    ContDiff ℝ ∞ ((hairerCanonicalData (κ := κ) N noise).globalPiBasis τ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hp : ContDiff ℝ ∞ D.globalPsi := contDiff_hairerConvolution N noise.smooth
  have hs : ContDiff ℝ ∞ D.globalPsiSq := hp.mul hp
  have hc : ContDiff ℝ ∞ D.globalPsiCube := hs.mul hp
  have hi : ContDiff ℝ ∞ D.globalIPsi := contDiff_hairerConvolution N hp
  have his : ContDiff ℝ ∞ D.globalIPsiSq := contDiff_hairerConvolution N hs
  have hic : ContDiff ℝ ∞ D.globalIPsiCube := contDiff_hairerConvolution N hc
  change ContDiff ℝ ∞ (D.globalPiBasis τ)
  cases τ with
  | one => exact contDiff_const
  | noise => exact noise.smooth
  | x0 => exact coord_smooth 0
  | x i => exact coord_smooth i.succ
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      exact (coord_smooth i.succ).mul (coord_smooth j.succ)
  | psi => exact hp
  | psiSq => exact hs
  | psiCube => exact hc
  | psiX i => exact hp.mul (coord_smooth i.succ)
  | psiSqX i => exact hs.mul (coord_smooth i.succ)
  | iPsi => exact hi
  | iPsiSq => exact his
  | iPsiCube => exact hic
  | iPsiPsi => exact hi.mul hp
  | iPsiPsiSq => exact hi.mul hs
  | iPsiSqPsi => exact his.mul hp
  | iPsiSqPsiSq => exact his.mul hs
  | iPsiCubePsi => exact hic.mul hp
  | iPsiCubePsiSq => exact hic.mul hs
  | iPsiCubeSq => exact hic.mul hic

open scoped ContDiff in
/-- Every unbased symbol has polynomial growth, derived from the noise
growth and the actual causal convolution (not from model-bound data). -/
theorem canonicalGlobalPiBasis_growth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (τ : Symbol) :
    PolyBounded ((hairerCanonicalData (κ := κ) N noise).globalPiBasis τ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hps : ContDiff ℝ ∞ D.globalPsi := contDiff_hairerConvolution N noise.smooth
  have hp : PolyBounded D.globalPsi := polyBounded_hairerConvolution N noise.smooth hf
  have hs : PolyBounded D.globalPsiSq := canonicalPolyBounded_mul hp hp
  have hc : PolyBounded D.globalPsiCube := canonicalPolyBounded_mul hs hp
  have hi : PolyBounded D.globalIPsi := polyBounded_hairerConvolution N hps hp
  have his : PolyBounded D.globalIPsiSq :=
    polyBounded_hairerConvolution N (hps.mul hps) hs
  have hic : PolyBounded D.globalIPsiCube :=
    polyBounded_hairerConvolution N ((hps.mul hps).mul hps) hc
  change PolyBounded (D.globalPiBasis τ)
  cases τ with
  | one => exact one_growth
  | noise => exact hf
  | x0 => exact coord_growth 0
  | x i => exact coord_growth i.succ
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      exact canonicalPolyBounded_mul (coord_growth i.succ) (coord_growth j.succ)
  | psi => exact hp
  | psiSq => exact hs
  | psiCube => exact hc
  | psiX i => exact canonicalPolyBounded_mul hp (coord_growth i.succ)
  | psiSqX i => exact canonicalPolyBounded_mul hs (coord_growth i.succ)
  | iPsi => exact hi
  | iPsiSq => exact his
  | iPsiCube => exact hic
  | iPsiPsi => exact canonicalPolyBounded_mul hi hp
  | iPsiPsiSq => exact canonicalPolyBounded_mul hi hs
  | iPsiSqPsi => exact canonicalPolyBounded_mul his hp
  | iPsiSqPsiSq => exact canonicalPolyBounded_mul his hs
  | iPsiCubePsi => exact canonicalPolyBounded_mul hic hp
  | iPsiCubePsiSq => exact canonicalPolyBounded_mul hic hs
  | iPsiCubeSq => exact canonicalPolyBounded_mul hic hic

end RegularityStructures.Phi43

end
