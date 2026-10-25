/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorBridge
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Iterated directional derivatives along a list of directions

`lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`, where `D_d f = x ↦ f'(x) d` (`dirDeriv`).  For smooth
`f` this agrees with `iteratedFDeriv ℝ n f w (fun i => L.get i)`, and it interacts simply with
composition by continuous linear maps, sign changes and scalar rescalings of the directions.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace RegularityStructures

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`. -/
def lineIter : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | d :: L, f => dirDeriv d (lineIter L f)

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
theorem lineIter_nil (f : E → ℝ) : lineIter [] f = f := rfl

@[simp]
theorem lineIter_cons (d : E) (L : List E) (f : E → ℝ) :
    lineIter (d :: L) f = dirDeriv d (lineIter L f) := rfl

theorem contDiff_dirDeriv_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (d : E) :
    ContDiff ℝ ∞ (dirDeriv d f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_lineIter {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : List E) :
    ContDiff ℝ ∞ (lineIter L f) := by
  induction L with
  | nil => exact hf
  | cons d L ih => exact contDiff_dirDeriv_of_contDiff ih d

theorem hasCompactSupport_lineIter {f : E → ℝ} (hf : HasCompactSupport f) (L : List E) :
    HasCompactSupport (lineIter L f) := by
  induction L with
  | nil => exact hf
  | cons d L ih => exact HasCompactSupport.fderiv_apply ℝ ih d

theorem lineIter_append (A B : List E) (f : E → ℝ) :
    lineIter (A ++ B) f = lineIter A (lineIter B f) := by
  induction A with
  | nil => rfl
  | cons d A ih => simp [ih]

theorem dirDeriv_comp_clm {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (A : F →L[ℝ] E) (d : F) :
    dirDeriv d (g ∘ A) = dirDeriv (A d) g ∘ A := by
  funext x
  have h := ((hg.differentiable (by simp)) (A x)).hasFDerivAt.comp x A.hasFDerivAt
  simp only [dirDeriv, Function.comp_apply]
  rw [show fderiv ℝ (g ∘ A) x = _ from h.fderiv]
  rfl

/-- Composition with a continuous linear map `A` maps the directions by `A`. -/
theorem lineIter_comp_clm {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (A : F →L[ℝ] E) (L : List F) :
    lineIter L (g ∘ A) = lineIter (L.map A) g ∘ A := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [lineIter_cons, ih, List.map_cons]
    exact dirDeriv_comp_clm (contDiff_lineIter hg _) A d

theorem dirDeriv_const_smul {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (d : E) (c : ℝ) :
    dirDeriv d (c • f) = c • dirDeriv d f := by
  funext x
  simp only [dirDeriv, Pi.smul_apply]
  rw [fderiv_const_smul ((hf.differentiable (by simp)) x)]
  simp

theorem dirDeriv_smul_dir (f : E → ℝ) (d : E) (c : ℝ) :
    dirDeriv (c • d) f = c • dirDeriv d f := by
  funext x
  simp [dirDeriv]

theorem lineIter_const_smul {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (L : List E) :
    lineIter L (c • f) = c • lineIter L f := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [lineIter_cons, ih]
    exact dirDeriv_const_smul (contDiff_lineIter hf L) d c

/-- Rescaling each direction by a scalar rescales the derivative by the product of the scalars. -/
theorem lineIter_map_smul {ι : Type*} {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ι → ℝ) (d : ι → E)
    (J : List ι) :
    lineIter (J.map fun j => r j • d j) f = (J.map r).prod • lineIter (J.map d) f := by
  induction J with
  | nil => simp
  | cons j J ih =>
    simp only [List.map_cons, lineIter_cons, ih, List.prod_cons]
    rw [dirDeriv_smul_dir, dirDeriv_const_smul (contDiff_lineIter hf _), smul_smul, mul_comm]

/-- Reversing all directions multiplies by `(-1)^n`. -/
theorem lineIter_map_neg {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : List E) :
    lineIter (L.map Neg.neg) f = ((-1 : ℝ) ^ L.length) • lineIter L f := by
  have := lineIter_map_smul (ι := E) hf (fun _ => (-1 : ℝ)) id L
  simpa [List.map_const', List.prod_replicate] using this

theorem iteratedFDeriv_get_eq_lineIter {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : List E) :
    (fun w => iteratedFDeriv ℝ L.length f w (fun i => L.get i)) = lineIter L f := by
  induction L with
  | nil => funext w; simp [iteratedFDeriv_zero_apply]
  | cons d L ih =>
    funext w
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ L.length f) w :=
      (hf.differentiable_iteratedFDeriv (m := L.length)
        (by exact_mod_cast ENat.natCast_lt_top _)) w
    rw [lineIter_cons, ← ih, dirDeriv, fderiv_continuousMultilinear_apply_const_apply hd]
    exact iteratedFDeriv_succ_apply_left (n := L.length) (fun i => (d :: L).get i)

end RegularityStructures

end
