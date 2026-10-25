/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.Torus.KernelBoundsGeometry
import RegularityStructures.PDE.SmoothDense
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lifts of torus increments

For `a : Fin 3 → ℝ` the torus point `(t, torusProj a)` has parabolic size at most `‖(t, a)‖_𝔰`
(`torusParabolicSize_proj_le`), and every `h : SpaceTime` has a lift `a` with `|aᵢ| ≤ 1/2` and
`‖(h.1, a)‖_𝔰 ≤ (9/5) s(h)` (`exists_torusLift_norm_le`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The spatial norm of the projection is at most the `ℓ¹` norm of any lift. -/
theorem torusSpatialNorm_proj_le_sum_abs (a : Fin 3 → ℝ) :
    torusSpatialNorm (torusProj a) ≤ ∑ i, |a i| := by
  have hc : ∀ i, |torusCenteredRep (torusProj a) i| ≤ |a i| := by
    intro i
    have hab : torusProj (torusCenteredRep (torusProj a)) = torusProj a :=
      RegularityStructures.torusProj_torusCenteredRep _
    obtain ⟨n, hn⟩ := RegularityStructures.PDE.exists_int_of_torusProj_eq hab i
    have := sq_centered_add_int_ge (torusCenteredRep_mem_Icc (torusProj a) i) n
    rw [← hn] at this
    exact sq_le_sq.1 this
  have hsum0 : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold torusSpatialNorm
  rw [Real.sqrt_le_left hsum0]
  unfold sqNorm3
  calc ∑ i, torusCenteredRep (torusProj a) i ^ 2
      = ∑ i, |torusCenteredRep (torusProj a) i| ^ 2 := by simp only [sq_abs]
    _ ≤ (∑ i, |torusCenteredRep (torusProj a) i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ (∑ i, |a i|) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _)
          (Finset.sum_le_sum fun i _ => hc i) 2

/-- The parabolic size of a projected increment is at most the size of the lift. -/
theorem torusParabolicSize_proj_le (t : ℝ) (a : Fin 3 → ℝ) :
    torusParabolicSize (t, torusProj a) ≤ parabolicNorm (t, a) := by
  unfold torusParabolicSize parabolicNorm
  have := torusSpatialNorm_proj_le_sum_abs a
  simp only
  linarith

/-- The `ℓ¹` norm of the centred representative is at most `9/5` of the torus spatial norm. -/
theorem torusCenteredRep_sum_abs_le (x : Torus3) :
    ∑ i, |torusCenteredRep x i| ≤ 9 / 5 * torusSpatialNorm x := by
  have hs := torusSpatialNorm_nonneg x
  have hsq := torusSpatialNorm_sq x
  have hcs : (∑ i, |torusCenteredRep x i|) ^ 2 ≤ 3 * ∑ i, |torusCenteredRep x i| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |torusCenteredRep x i|)
    simpa using this
  have hcs' : ∑ i, |torusCenteredRep x i| ^ 2 = torusSpatialNorm x ^ 2 := by
    rw [hsq]; unfold sqNorm3; simp only [sq_abs]
  rw [hcs'] at hcs
  have h2 : (∑ i, |torusCenteredRep x i|) ^ 2 ≤ (9 / 5 * torusSpatialNorm x) ^ 2 := by
    have : 0 ≤ torusSpatialNorm x ^ 2 := sq_nonneg _
    calc _ ≤ 3 * torusSpatialNorm x ^ 2 := hcs
      _ ≤ (9 / 5 * torusSpatialNorm x) ^ 2 := by rw [mul_pow]; linarith
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
    (by norm_num)).1 h2

/-- Every torus increment has a lift with coordinates in `[-1/2, 1/2]` and size at most
`(9/5) s(h)`. -/
theorem exists_torusLift_norm_le (h : SpaceTime) :
    ∃ a : Fin 3 → ℝ, (∀ i, |a i| ≤ 1 / 2) ∧ torusProj a = h.2 ∧
      parabolicNorm (h.1, a) ≤ 9 / 5 * torusParabolicSize h := by
  refine ⟨torusCenteredRep h.2, fun i => abs_le.2 ⟨(torusCenteredRep_mem_Icc h.2 i).1,
    (torusCenteredRep_mem_Icc h.2 i).2⟩, RegularityStructures.torusProj_torusCenteredRep h.2, ?_⟩
  unfold parabolicNorm torusParabolicSize
  have := torusCenteredRep_sum_abs_le h.2
  have h0 := Real.sqrt_nonneg |h.1|
  simp only
  linarith

end RegularityStructures.Phi43

end
