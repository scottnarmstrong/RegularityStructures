/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Kernel.GeneratorIBP
public import RegularityStructures.Analysis.Kernel.GeneratorStep
public import RegularityStructures.Analysis.Kernel.GeneratorBridge
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Algebra of directional derivatives

Directional derivatives of smooth functions on `ℝ⁴` are linear, commute with each other
(`dirDeriv_comm`), with shifts, and with the generator `parabolicGenerator`.  Consequently
`lineIter L f` only depends on the multiset of directions (`lineIter_perm`).  These facts are used
for the Taylor expansion of the shells in Hairer's Lemma 5.18/5.19 (`Taylor*.lean`).
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem dirDeriv_add {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (d : ParabolicSpace) :
    dirDeriv d (fun w => f w + g w) = fun w => dirDeriv d f w + dirDeriv d g w := by
  funext w
  simp only [dirDeriv]
  rw [fderiv_fun_add ((hf.differentiable (by simp)) w) ((hg.differentiable (by simp)) w)]
  simp

theorem dirDeriv_sub {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (d : ParabolicSpace) :
    dirDeriv d (fun w => f w - g w) = fun w => dirDeriv d f w - dirDeriv d g w := by
  funext w
  simp only [dirDeriv]
  rw [fderiv_fun_sub ((hf.differentiable (by simp)) w) ((hg.differentiable (by simp)) w)]
  simp

theorem dirDeriv_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ParabolicSpace → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (d : ParabolicSpace) :
    dirDeriv d (fun w => ∑ i ∈ s, f i w) = fun w => ∑ i ∈ s, dirDeriv d (f i) w := by
  funext w
  simp only [dirDeriv]
  rw [fderiv_fun_sum fun i hi => (hf i hi).differentiable (by simp) w]
  simp

theorem dirDeriv_comm {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (d e : ParabolicSpace) :
    dirDeriv d (dirDeriv e f) = dirDeriv e (dirDeriv d f) := by
  funext w
  have hsym := ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := w)) (n := ∞)
    (by simp [minSmoothness_of_isRCLikeNormedField]) d e
  have hd : ∀ a v : ParabolicSpace, dirDeriv a (dirDeriv v f) w = fderiv ℝ (fderiv ℝ f) w a v := by
    intro a v
    have : DifferentiableAt ℝ (fderiv ℝ f) w :=
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) w
    simp only [dirDeriv]
    have h3 : fderiv ℝ (fun x => fderiv ℝ f x v) w a = fderiv ℝ (fderiv ℝ f) w a v := by
      rw [fderiv_clm_apply this (differentiableAt_const v)]
      simp
    exact h3
  rw [hd d e, hd e d]
  exact hsym

theorem dirDeriv_shift {f : ParabolicSpace → ℝ} (d a : ParabolicSpace) :
    dirDeriv d (fun w => f (w + a)) = fun w => dirDeriv d f (w + a) := by
  funext w
  simp only [dirDeriv]
  rw [fderiv_comp_add_right]

theorem lineIter_dirDeriv_comm {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (e : ParabolicSpace)
    (K : List ParabolicSpace) : lineIter K (dirDeriv e f) = dirDeriv e (lineIter K f) := by
  induction K with
  | nil => rfl
  | cons d K ih =>
    rw [lineIter_cons, lineIter_cons, ih]
    exact dirDeriv_comm (contDiff_lineIter hf K) d e

theorem lineIter_perm {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) {L L' : List ParabolicSpace}
    (h : L.Perm L') : lineIter L f = lineIter L' f := by
  induction h with
  | nil => rfl
  | cons d _ ih => simp [ih]
  | swap d e L =>
    simp only [lineIter_cons]
    exact (dirDeriv_comm (contDiff_lineIter hf L) d e).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lineIter_shift {f : ParabolicSpace → ℝ} (a : ParabolicSpace) (K : List ParabolicSpace) :
    lineIter K (fun w => f (w + a)) = fun w => lineIter K f (w + a) := by
  induction K with
  | nil => rfl
  | cons d K ih => rw [lineIter_cons, lineIter_cons, ih, dirDeriv_shift]

theorem lineIter_add {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (K : List ParabolicSpace) :
    lineIter K (fun w => f w + g w) = fun w => lineIter K f w + lineIter K g w := by
  induction K with
  | nil => rfl
  | cons d K ih =>
    rw [lineIter_cons, ih, lineIter_cons, lineIter_cons]
    exact dirDeriv_add (contDiff_lineIter hf K) (contDiff_lineIter hg K) d

theorem lineIter_sub {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (K : List ParabolicSpace) :
    lineIter K (fun w => f w - g w) = fun w => lineIter K f w - lineIter K g w := by
  induction K with
  | nil => rfl
  | cons d K ih =>
    rw [lineIter_cons, ih, lineIter_cons, lineIter_cons]
    exact dirDeriv_sub (contDiff_lineIter hf K) (contDiff_lineIter hg K) d

theorem lineIter_const_mul {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (K : List ParabolicSpace) : lineIter K (fun w => c * f w) = fun w => c * lineIter K f w :=
  lineIter_const_smul hf c K

theorem lineIter_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ParabolicSpace → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (K : List ParabolicSpace) :
    lineIter K (fun w => ∑ i ∈ s, f i w) = fun w => ∑ i ∈ s, lineIter K (f i) w := by
  induction K with
  | nil => rfl
  | cons d K ih =>
    rw [lineIter_cons, ih, dirDeriv_finset_sum s (fun i hi => contDiff_lineIter (hf i hi) K)]
    rfl

theorem lineIter_replicate (e : ParabolicSpace) (p : ℕ) (f : ParabolicSpace → ℝ) :
    lineIter (List.replicate p e) f = (dirDeriv e)^[p] f := by
  induction p with
  | zero => rfl
  | succ p ih => rw [List.replicate_succ, lineIter_cons, ih, Function.iterate_succ_apply']

end RegularityStructures

end
