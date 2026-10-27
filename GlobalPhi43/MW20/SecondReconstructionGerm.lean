/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.SecondProductGerm
public import GlobalPhi43.Local.Algebra

/-!
# An auxiliary germ matching the Lemma 2.10 reconstruction estimate

The counterterm sign in [MW20, (5.15)] does not yield the subsequent
increment identity; the defect of that printed germ is calculated below.
An auxiliary germ with the opposite counterterm sign gives the identity
for reconstruction with the same hypotheses and conclusion of Lemma 2.10.
-/

public section

open scoped ContDiff

namespace GlobalPhi43.MW20

variable {E ι : Type*} [Fintype ι]

/-- Alternative auxiliary germ: its counterterm is +3C₂(v(x)-v(y)), rather
than the minus sign in the printed (5.15). -/
@[expose] def secondReconstructionGerm (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x y : E) : ℝ :=
  secondProductGerm v Y Z V ν X C₂ x y + 6 * C₂ * (v x - v y)

@[simp] theorem secondReconstructionGerm_diag (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x : E) :
    secondReconstructionGerm v Y Z V ν X C₂ x x = v x * V x := by
  simp [secondReconstructionGerm]

/-- Exact defect of the printed germ relative to the negative of the claimed
source coherence expression. The project A composite has Y(y)-Y(z), not its
opposite. No renormalisation constant can be discarded in this identity. -/
theorem secondProductGerm_source_defect (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x z y : E) :
    (secondProductGerm v Y Z V ν X C₂ x y - secondProductGerm v Y Z V ν X C₂ z y) +
      (3 * (v x - v z) * ((Y y - Y z) * V y - C₂) +
       (Local.expansion v Y Z x z - ∑ i, ν x i * (X z i - X x i)) * V y -
       (∑ i, (ν x i - ν z i) * (X y i - X z i)) * V y) = -6 * C₂ * (v x - v z) := by
  rw [secondProductGerm_increment, Local.expansion_eq]
  ring

/-- Exact coherence of the corrected auxiliary germ, using the actual
recentered A composite and shared local affine remainder. -/
theorem secondReconstructionGerm_increment (v Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x z y : E) :
    secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y =
      -(3 * (v x - v z) * ((Y y - Y z) * V y - C₂)) -
      (Local.expansion v Y Z x z - ∑ i, ν x i * (X z i - X x i)) * V y +
      (∑ i, (ν x i - ν z i) * (X y i - X z i)) * V y := by
  unfold secondReconstructionGerm
  have h := secondProductGerm_source_defect v Y Z V ν X C₂ x z y
  linear_combination h

/-- Exact signed estimate identity for the stated Lemma 2.10 left side. The source
A and D composites have their original counterterms; no extra C₂ budget is
introduced by the alternative auxiliary germ. -/
theorem secondReconstructionGerm_consumer_identity (v J Y Z V : E → ℝ)
    (ν X : E → ι → ℝ) (C₂ : ℝ) (x y : E) :
    (v y - v x) * V y + 3 * C₂ * (v y + J y) =
      -(secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y) -
      ((Z y - Z x) * V y - 3 * C₂ * J y) -
      3 * v x * ((Y y - Y x) * V y - C₂) +
      (∑ i, ν x i * (X y i - X x i)) * V y := by
  have h := secondReconstructionGerm_increment v Y Z V ν X C₂ x y y
  simp only [secondReconstructionGerm_diag, sub_self, mul_zero,
    Finset.sum_const_zero] at h
  rw [Local.expansion_eq] at h
  linear_combination h

/-- Standing smoothness is preserved by the alternative auxiliary germ. -/
theorem secondReconstructionGerm_contDiff [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (hV : ContDiff ℝ ∞ V) (hν : ContDiff ℝ ∞ ν) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun p : E × E => secondReconstructionGerm v Y Z V ν X C₂ p.1 p.2) := by
  exact (secondProductGerm_contDiff v Y Z V ν X C₂ hv hY hZ hV hν hX).add
    (contDiff_const.mul ((hv.comp contDiff_fst).sub (hv.comp contDiff_snd)))

end GlobalPhi43.MW20

end
