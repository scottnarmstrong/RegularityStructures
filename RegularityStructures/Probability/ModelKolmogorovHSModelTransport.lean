/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4ModelMollify
public import RegularityStructures.Abstract.Model

/-!
# Isolating lower-sector covariance terms

Hairer--Steele, arXiv:2301.10081v3, Lemma B.4, equation (B.5), and
Corollary B.5 transport evaluations from the fixed base point to the
evaluation point. Graded unipotence makes the top coefficient one and
kills every other coefficient of equal or greater degree. Thus only
strictly lower-sector terms remain. The two-model identity separates
the lower Pi difference and the Gamma difference without discarding
either contribution.
-/

public section

open MeasureTheory

namespace RegularityStructures.Model

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- Transport away from the diagonal involves only strictly lower-degree coordinates. -/
theorem regPi_single_sub_diag_eq_lower
    (M : Model 𝒯 K) (x y : E) (i : ι) (u : ℝ) :
    M.regPi x (Pi.single i 1) u y - M.regPi y (Pi.single i 1) u y =
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < 𝒯.deg i),
        M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y := by
  classical
  rw [M.regPi_single_eq_sum_gammaMap x y i u y,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 𝒯.deg j < 𝒯.deg i)]
  have he : (∑ j ∈ Finset.univ.filter (fun j => ¬𝒯.deg j < 𝒯.deg i),
      M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y) =
        M.regPi y (Pi.single i 1) u y := by
    rw [Finset.sum_eq_single i]
    · rw [M.gammaMap_single_apply_self, one_mul]
    · intro j hj hji
      rw [M.gammaMap_single_apply_of_le x y hji (not_lt.1 (Finset.mem_filter.1 hj).2), zero_mul]
    · intro hi
      exact (hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, not_lt_of_ge le_rfl⟩)).elim
  rw [he]
  ring

end RegularityStructures.Model

end
