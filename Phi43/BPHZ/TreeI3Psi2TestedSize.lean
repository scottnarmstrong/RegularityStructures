/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.PDE.SmoothDense

/-!
# The sharp triangle inequality for the parabolic size on `ℝ × T³`

The repository lemma `torusParabolicSize_sub_le` has the constant `4`.  Here we prove the sharp
inequalities `s(a + b) ≤ s(a) + s(b)` and `s(-a) ≤ s(a)` for `s = torusParabolicSize`, which give
`s(u + h) ≥ s(u) - s(h)`.  The key point is that the centred representative is of minimal
absolute value in its class coordinatewise.
-/

public section

namespace RegularityStructures

private theorem abs_torusCenteredRep_le_of_torusProj_eq {x : Torus3} {r : Fin 3 → ℝ}
    (h : torusProj r = x) (i : Fin 3) : |torusCenteredRep x i| ≤ |r i| := by
  have hc := torusCenteredRep_mem_Ico x i
  have hp : torusProj (torusCenteredRep x) = torusProj r := by
    rw [torusProj_torusCenteredRep, h]
  obtain ⟨n, hn⟩ := PDE.exists_int_of_torusProj_eq hp i
  have hcabs : |torusCenteredRep x i| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩
  rcases lt_trichotomy n 0 with hneg | hz | hpos
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    refine hcabs.trans ?_
    cases abs_cases (r i) <;> linarith [hc.2]
  · subst hz
    simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    refine hcabs.trans ?_
    cases abs_cases (r i) <;> linarith [hc.1]

private theorem torusSpatialNorm_le_sqrt_of_torusProj_eq {x : Torus3} {r : Fin 3 → ℝ}
    (h : torusProj r = x) : torusSpatialNorm x ≤ √(sqNorm3 r) := by
  unfold torusSpatialNorm
  refine Real.sqrt_le_sqrt ?_
  unfold sqNorm3
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sq_abs (torusCenteredRep x i), ← sq_abs (r i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_torusCenteredRep_le_of_torusProj_eq h i) 2

private theorem sqrt_sqNorm3_add_le (a b : Fin 3 → ℝ) :
    √(sqNorm3 (a + b)) ≤ √(sqNorm3 a) + √(sqNorm3 b) := by
  have hA : 0 ≤ sqNorm3 a := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ sqNorm3 b := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hab : ∑ i, a i * b i ≤ √(sqNorm3 a) * √(sqNorm3 b) := by
    rw [← Real.sqrt_mul hA]
    refine Real.le_sqrt_of_sq_le ?_
    unfold sqNorm3
    exact hcs
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have e : sqNorm3 (a + b) = sqNorm3 a + 2 * ∑ i, a i * b i + sqNorm3 b := by
    unfold sqNorm3
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

/-- The spatial norm on `T³` satisfies the triangle inequality with constant one. -/
theorem torusSpatialNorm_add_le_add (x y : Torus3) :
    torusSpatialNorm (x + y) ≤ torusSpatialNorm x + torusSpatialNorm y := by
  have hp : torusProj (torusCenteredRep x + torusCenteredRep y) = x + y := by
    funext i
    simp only [torusProj, Pi.add_apply, AddCircle.coe_add]
    have h1 := congrFun (torusProj_torusCenteredRep x) i
    have h2 := congrFun (torusProj_torusCenteredRep y) i
    simp only [torusProj] at h1 h2
    rw [h1, h2]
  refine (torusSpatialNorm_le_sqrt_of_torusProj_eq hp).trans ?_
  exact sqrt_sqNorm3_add_le _ _

/-- The spatial norm on `T³` is symmetric (at most). -/
theorem torusSpatialNorm_neg_le_self (x : Torus3) : torusSpatialNorm (-x) ≤ torusSpatialNorm x := by
  have hp : torusProj (-torusCenteredRep x) = -x := by
    funext i
    simp only [torusProj, Pi.neg_apply, AddCircle.coe_neg]
    have h1 := congrFun (torusProj_torusCenteredRep x) i
    simp only [torusProj] at h1
    rw [h1]
  refine (torusSpatialNorm_le_sqrt_of_torusProj_eq hp).trans (le_of_eq ?_)
  unfold torusSpatialNorm sqNorm3
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- **Sharp triangle inequality** for the parabolic size. -/
theorem torusParabolicSize_add_le_add (a b : SpaceTime) :
    torusParabolicSize (a + b) ≤ torusParabolicSize a + torusParabolicSize b := by
  unfold torusParabolicSize
  have ht : √|(a + b).1| ≤ √|a.1| + √|b.1| := by
    have habs : |(a + b).1| ≤ |a.1| + |b.1| := abs_add_le _ _
    refine (Real.sqrt_le_sqrt habs).trans ?_
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (abs_nonneg _)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg |a.1|) (Real.sqrt_nonneg |b.1|)]
  have hs := torusSpatialNorm_add_le_add a.2 b.2
  simp only [Prod.fst_add, Prod.snd_add] at ht ⊢
  linarith

/-- `s(-a) ≤ s(a)`. -/
theorem torusParabolicSize_neg_le_self (a : SpaceTime) :
    torusParabolicSize (-a) ≤ torusParabolicSize a := by
  unfold torusParabolicSize
  have := torusSpatialNorm_neg_le_self a.2
  simp only [Prod.fst_neg, Prod.snd_neg, abs_neg]
  linarith

/-- `s(u) - s(h) ≤ s(u + h)`. -/
theorem torusParabolicSize_sub_le_add (u h : SpaceTime) :
    torusParabolicSize u - torusParabolicSize h ≤ torusParabolicSize (u + h) := by
  have h1 := torusParabolicSize_add_le_add (u + h) (-h)
  have h2 := torusParabolicSize_neg_le_self h
  simp only [add_neg_cancel_right] at h1
  linarith

/-- `s(u) - s(w) ≤ s(u - w)`. -/
theorem torusParabolicSize_sub_le_sub (u w : SpaceTime) :
    torusParabolicSize u - torusParabolicSize w ≤ torusParabolicSize (u - w) := by
  have h1 := torusParabolicSize_add_le_add (u - w) w
  simp only [sub_add_cancel] at h1
  linarith

/-- `s(u + h) ≤ s(u) + s(h)`, in the `sub` form. -/
theorem torusParabolicSize_sub_le_add_self (u w : SpaceTime) :
    torusParabolicSize (u - w) ≤ torusParabolicSize u + torusParabolicSize w := by
  rw [sub_eq_add_neg]
  exact (torusParabolicSize_add_le_add u (-w)).trans
    (add_le_add_right (torusParabolicSize_neg_le_self w) _)

end RegularityStructures

end
