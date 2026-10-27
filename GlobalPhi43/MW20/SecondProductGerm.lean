/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import GlobalPhi43.MW20.ProductGerms
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Algebra of the second product germ in MW20 §5.2.3

The spatial correction is written as an actual finite dot product. J, V, Y, Z
and the testing kernel are not conflated. These are exact algebraic identities;
the analytic reconstruction application still needs smooth carriers and all
source seminorm estimates.
-/

public section

open scoped ContDiff

namespace GlobalPhi43.MW20

variable {E ι : Type*} [Fintype ι]

/-- The germ (5.15), with `X(y-x) = X y - X x`. The plus sign on the spatial
correction equals the source's minus sign on `ν(x)·X(x-y)`. -/
def secondProductGerm (v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ)
    (x y : E) : ℝ :=
  (v x + Z x - Z y + 3 * v x * (Y x - Y y) +
    ∑ i, ν x i * (X y i - X x i)) * V y - 3 * C₂ * (v x - v y)

@[simp] theorem secondProductGerm_diag (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x : E) :
    secondProductGerm v Y Z V ν X C₂ x x = v x * V x := by
  simp [secondProductGerm]

/-- The three coherence terms are the recentered YV composite, the affine
remainder U(x,z), and the increment of ν tested against the spatial coordinate.
This identity keeps the signed counterterm in the recentered composite. -/
theorem secondProductGerm_increment (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x z y : E) :
    secondProductGerm v Y Z V ν X C₂ x y - secondProductGerm v Y Z V ν X C₂ z y =
      3 * (v x - v z) * ((Y z - Y y) * V y - C₂) -
      (v z - v x + Z z - Z x + 3 * v x * (Y z - Y x) -
        ∑ i, ν x i * (X z i - X x i)) * V y +
      (∑ i, (ν x i - ν z i) * (X y i - X z i)) * V y := by
  have hsp : (∑ i, ν x i * (X y i - X x i)) -
      (∑ i, ν z i * (X y i - X z i)) =
      (∑ i, ν x i * (X z i - X x i)) +
      ∑ i, (ν x i - ν z i) * (X y i - X z i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold secondProductGerm
  linear_combination (V y) * hsp

/-- Smooth local fields yield the smooth two-variable germ required by the
standing §2.2 convention in the second reconstruction application. -/
theorem secondProductGerm_contDiff [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (hV : ContDiff ℝ ∞ V) (hν : ContDiff ℝ ∞ ν) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun p : E × E => secondProductGerm v Y Z V ν X C₂ p.1 p.2) := by
  have hsp : ContDiff ℝ ∞ (fun p : E × E =>
      ∑ i, ν p.1 i * (X p.2 i - X p.1 i)) := by
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp (hν.comp contDiff_fst)).mul
      (((contDiff_apply ℝ ℝ i).comp (hX.comp contDiff_snd)).sub
        ((contDiff_apply ℝ ℝ i).comp (hX.comp contDiff_fst)))
  change ContDiff ℝ ∞ (fun p : E × E =>
    (v p.1 + Z p.1 - Z p.2 + 3 * v p.1 * (Y p.1 - Y p.2) +
      ∑ i, ν p.1 i * (X p.2 i - X p.1 i)) * V p.2 - 3 * C₂ * (v p.1 - v p.2))
  exact (((((hv.comp contDiff_fst).add (hZ.comp contDiff_fst)).sub
    (hZ.comp contDiff_snd)).add ((contDiff_const.mul (hv.comp contDiff_fst)).mul
      ((hY.comp contDiff_fst).sub (hY.comp contDiff_snd)))).add hsp |>.mul
        (hV.comp contDiff_snd)).sub
          (contDiff_const.mul ((hv.comp contDiff_fst).sub (hv.comp contDiff_snd)))

end GlobalPhi43.MW20

end
