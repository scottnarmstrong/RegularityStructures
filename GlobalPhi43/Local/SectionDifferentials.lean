/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalCoefficientSmooth
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Joint derivative fields for the sections U(x,·). These fields allow
compactness to give finite Taylor bounds from the standing local smoothness. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Filter
open scoped ContDiff Topology

abbrev GermPoint := ParabolicSpace × ParabolicSpace

def sectionSpatialInsert : (Fin 3 → ℝ) →L[ℝ] GermPoint :=
  (0 : (Fin 3 → ℝ) →L[ℝ] ParabolicSpace).prod
    ((0 : (Fin 3 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))

def sectionSpaceDerivative (U : GermPoint → ℝ) (p : GermPoint) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ U p).comp sectionSpatialInsert

def sectionSpaceHessian (U : GermPoint → ℝ) (p : GermPoint) :
    (Fin 3 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
  (fderiv ℝ (sectionSpaceDerivative U) p).comp sectionSpatialInsert

def sectionTimeDerivative (U : GermPoint → ℝ) (p : GermPoint) : ℝ :=
  fderiv ℝ U p (0, (1, 0))

theorem section_embedding_hasFDerivAt (x : ParabolicSpace) (t : ℝ) (z : Fin 3 → ℝ) :
    HasFDerivAt (fun w : Fin 3 → ℝ => (x, (t, w))) sectionSpatialInsert z := by
  exact (hasFDerivAt_const x z).prodMk ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))

theorem sectionSpaceDerivative_contDiffAt (U : GermPoint → ℝ) (p : GermPoint)
    (hU : ContDiffAt ℝ ∞ U p) : ContDiffAt ℝ ∞ (sectionSpaceDerivative U) p := by
  exact (hU.fderiv_right (by simp)).clm_comp contDiffAt_const

theorem sectionSpaceHessian_contDiffAt (U : GermPoint → ℝ) (p : GermPoint)
    (hU : ContDiffAt ℝ ∞ U p) : ContDiffAt ℝ ∞ (sectionSpaceHessian U) p := by
  exact ((sectionSpaceDerivative_contDiffAt U p hU).fderiv_right (by simp)).clm_comp contDiffAt_const

theorem sectionTimeDerivative_contDiffAt (U : GermPoint → ℝ) (p : GermPoint)
    (hU : ContDiffAt ℝ ∞ U p) : ContDiffAt ℝ ∞ (sectionTimeDerivative U) p := by
  exact (hU.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem section_fderiv_eq (U : GermPoint → ℝ) (x : ParabolicSpace) (t : ℝ) (z : Fin 3 → ℝ)
    (hU : DifferentiableAt ℝ U (x, (t, z))) :
    fderiv ℝ (fun w => U (x, (t, w))) z = sectionSpaceDerivative U (x, (t, z)) := by
  exact (hU.hasFDerivAt.comp z (section_embedding_hasFDerivAt x t z)).fderiv

/-- The actual second spatial differential of each section is the joint
Hessian field, requiring smoothness only at the tested germ point. -/
theorem section_second_fderiv_eq (U : GermPoint → ℝ) (x : ParabolicSpace) (t : ℝ) (z : Fin 3 → ℝ)
    (hU : ContDiffAt ℝ ∞ U (x, (t, z))) :
    fderiv ℝ (fderiv ℝ (fun w => U (x, (t, w)))) z = sectionSpaceHessian U (x, (t, z)) := by
  have h₁ : ContDiffAt ℝ 1 U (x, (t, z)) := hU.of_le (by simp)
  have hd : ∀ᶠ p in 𝓝 (x, (t, z)), DifferentiableAt ℝ U p :=
    (h₁.eventually (by norm_num)).mono fun _ hp => hp.differentiableAt (by norm_num)
  have hm := (section_embedding_hasFDerivAt x t z).continuousAt.tendsto
  have heq : (fderiv ℝ (fun w => U (x, (t, w)))) =ᶠ[𝓝 z]
      (fun w => sectionSpaceDerivative U (x, (t, w))) := by
    filter_upwards [hm.eventually hd] with w hw
    exact section_fderiv_eq U x t w hw
  rw [heq.fderiv_eq]
  exact (((sectionSpaceDerivative_contDiffAt U _ hU).differentiableAt (by simp)).hasFDerivAt.comp z
    (section_embedding_hasFDerivAt x t z)).fderiv

/-- The actual scalar time derivative of the section is the joint time field. -/
theorem section_time_deriv_eq (U : GermPoint → ℝ) (x : ParabolicSpace) (t : ℝ) (q : Fin 3 → ℝ)
    (hU : DifferentiableAt ℝ U (x, (t, q))) :
    deriv (fun s => U (x, (s, q))) t = sectionTimeDerivative U (x, (t, q)) := by
  have hm : HasDerivAt (fun s : ℝ => (x, (s, q))) (0, (1, 0)) t := by
    exact (hasDerivAt_const t x).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t q))
  exact (hU.hasFDerivAt.comp_hasDerivAt t hm).deriv

end GlobalPhi43.Local
