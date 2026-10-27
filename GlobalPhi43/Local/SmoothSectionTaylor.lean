/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSectionBounds
public import GlobalPhi43.Local.ClosedPastBox
public import GlobalPhi43.Local.ParabolicAffineError

/-! Local smoothness and compact derivative bounds supply uniform section
Taylor errors on all the source's admissible past boxes. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric
open scoped ContDiff

theorem source_section_taylor (U : GermPoint → ℝ) {r d R S : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d) (hS : 0 ≤ S)
    (hU : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r, ContDiffAt ℝ ∞ U p)
    (hbound : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x R) :
    |U (x, y) - U (x, x) - sectionSpaceDerivative U (x, x) (y.2 - x.2)| ≤ 2 * S * R ^ 2 := by
  have hxD := cylinderInterior_mem_domain (hR.trans hRd) hx
  have hm (q : Fin 3 → ℝ) (hq : q ∈ closedBall x.2 R)
      (t : ℝ) (ht : t ∈ Icc (x.1 - R ^ 2) x.1) :
      (x, (t, q)) ∈ sourceCylinder r ×ˢ sourceCylinder r := by
    refine ⟨hxD, closed_past_box_mem_source hR hRd hx ht.1 ht.2 ?_⟩
    simpa only [mem_closedBall, dist_eq_norm] using hq
  have ht0 : x.1 ∈ Icc (x.1 - R ^ 2) x.1 := ⟨by nlinarith [sq_nonneg R], le_rfl⟩
  have hspace (q : Fin 3 → ℝ) (hq : q ∈ closedBall x.2 R) :
      ContDiffAt ℝ ∞ (fun w => U (x, (x.1, w))) q :=
    (hU _ (hm q hq x.1 ht0)).comp (f := fun w : Fin 3 → ℝ => (x, (x.1, w))) q (by fun_prop)
  have hb := parabolic_quadratic_taylor (fun z => U (x, z)) x y hR hS hy
    (by
      intro t ht
      exact ((hU _ (hm y.2 (by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
        exact (le_max_right _ _).trans hy.1.le) t ht)).differentiableAt (by simp)).comp
        (f := fun s : ℝ => (x, (s, y.2))) t (by fun_prop))
    (by
      intro t ht
      have hp := hm y.2 (by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
        exact (le_max_right _ _).trans hy.1.le) t ht
      rw [section_time_deriv_eq U x t y.2 ((hU _ hp).differentiableAt (by simp))]
      exact (hbound _ hp).1)
    (fun q hq => (hspace q hq).differentiableAt (by simp))
    (fun q hq => ((hspace q hq).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (by
      intro q hq
      rw [section_second_fderiv_eq U x x.1 q (hU _ (hm q hq x.1 ht0))]
      exact (hbound _ (hm q hq x.1 ht0)).2)
  have he := section_fderiv_eq U x x.1 x.2 ((hU _ ⟨hxD, hxD⟩).differentiableAt (by simp))
  simpa only [he, Prod.mk.eta] using hb

/-- This is the actual affine infimum, not an assumed approximation budget. -/
theorem source_section_affine_error (U : GermPoint → ℝ) {r d R S : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d) (hS : 0 ≤ S)
    (hU : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r, ContDiffAt ℝ ∞ U p)
    (hbound : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S)
    {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d) :
    pastAffineError (fun y => U (x, y)) x R ≤ ENNReal.ofReal (2 * S * R ^ 2) := by
  let L := sectionSpaceDerivative U (x, x)
  apply pastAffineError_le_of_bound _ x (U (x, x)) (fun i => L (Pi.single i 1))
  intro y hy
  have hb := source_section_taylor U hR hRd hS hU hbound hx hy
  have he : U (x, y) - spatialAffine x (U (x, x)) (fun i => L (Pi.single i 1)) y =
      U (x, y) - U (x, x) - L (y.2 - x.2) := by
    rw [spatialAffine, spatialLinear_eq_differential]
    simp only [Prod.snd_sub]
    ring
  simpa only [he] using hb

end GlobalPhi43.Local
