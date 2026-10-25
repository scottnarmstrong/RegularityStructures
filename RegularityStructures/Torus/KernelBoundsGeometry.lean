/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGaussian

/-!
# Elementary geometry of the centered torus representative

These lemmas make the parabolic triangle estimate explicit.  The centered representative is used
only for the Euclidean spatial norm; all quotient identities are discharged in `AddCircle`.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem torusProj_torusCenteredRep (x : Torus3) :
    torusProj (torusCenteredRep x) = x := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  funext i
  dsimp [torusProj]
  have hrep : ((torusRep x i : ℝ) : UnitAddCircle) = x i := by
    dsimp [torusRep]
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
      (y := (x i : UnitAddCircle))
  rw [← hrep]
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-(m i), ?_⟩
  have hi := congrFun hm i
  rw [hi]
  simp only [zsmul_eq_mul, Pi.add_apply]
  rw [Int.cast_neg]
  ring

theorem torusCenteredRep_sub_integer (x y : Torus3) (i : Fin 3) :
    ∃ n : ℤ, torusCenteredRep (x - y) i =
      torusCenteredRep x i - torusCenteredRep y i + (n : ℝ) := by
  let a : Fin 3 → ℝ := torusCenteredRep x
  let b : Fin 3 → ℝ := torusCenteredRep y
  let c : Fin 3 → ℝ := torusCenteredRep (x - y)
  have hxy : torusProj (a - b) = x - y := by
    ext j
    change ((a j - b j : ℝ) : UnitAddCircle) = (x j - y j)
    rw [AddCircle.coe_sub]
    change (torusProj a) j - (torusProj b) j = x j - y j
    rw [torusProj_torusCenteredRep x, torusProj_torusCenteredRep y]
  have hc : torusProj c = x - y := torusProj_torusCenteredRep (x - y)
  have hi : ((a i - b i : ℝ) : UnitAddCircle) = (c i : UnitAddCircle) := by
    have h := congrFun hxy i
    have h' := congrFun hc i
    exact h.trans h'.symm
  have hmem : a i - b i - c i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    (QuotientAddGroup.eq_iff_sub_mem.mp hi)
  rcases AddSubgroup.mem_zmultiples_iff.mp hmem with ⟨n, hn⟩
  refine ⟨-n, ?_⟩
  have hn' : (n : ℝ) = a i - b i - c i := by simpa using hn
  dsimp [a, b, c] at hn' ⊢
  rw [Int.cast_neg]
  linarith

theorem abs_torusCenteredRep_sub_le (x y : Torus3) (i : Fin 3) :
    |torusCenteredRep (x - y) i| ≤
      |torusCenteredRep x i| + |torusCenteredRep y i| := by
  obtain ⟨n, hn⟩ := torusCenteredRep_sub_integer x y i
  have ha := torusCenteredRep_mem_Icc x i
  have hb := torusCenteredRep_mem_Icc y i
  have hc := torusCenteredRep_mem_Icc (x - y) i
  have hnsmall : n = -1 ∨ n = 0 ∨ n = 1 := by
    have hnl : (-2 : ℤ) < n := by
      exact_mod_cast (show (-2 : ℝ) < (n : ℝ) by
        linarith [hn, ha.2, hb.1, hc.1])
    have hnu : n < (2 : ℤ) := by
      exact_mod_cast (show (n : ℝ) < (2 : ℝ) by
        linarith [hn, ha.1, hb.2, hc.2])
    omega
  rcases hnsmall with rfl | rfl | rfl
  · have hn' : torusCenteredRep (x - y) i =
        torusCenteredRep x i - torusCenteredRep y i - 1 := by
      rw [Int.cast_neg, Int.cast_one] at hn
      linarith [hn]
    rw [hn']
    by_cases h : 0 ≤ torusCenteredRep x i - torusCenteredRep y i - 1
    · rw [abs_of_nonneg h]
      by_cases hax : 0 ≤ torusCenteredRep x i
      · by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hax, abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonneg hax, abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · rw [abs_of_nonpos (le_of_not_ge hax)]
        by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
    · have hneg : torusCenteredRep x i - torusCenteredRep y i - 1 < 0 :=
        lt_of_not_ge h
      rw [abs_of_neg hneg]
      by_cases hax : 0 ≤ torusCenteredRep x i
      · by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hax, abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonneg hax, abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · rw [abs_of_neg (lt_of_not_ge hax)]
        by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
  · have hn' : torusCenteredRep (x - y) i =
        torusCenteredRep x i - torusCenteredRep y i := by simpa using hn
    rw [hn']
    simpa using (abs_sub_le (torusCenteredRep x i) 0 (torusCenteredRep y i))
  · have hn' : torusCenteredRep (x - y) i =
        torusCenteredRep x i - torusCenteredRep y i + 1 := by simpa using hn
    rw [hn']
    by_cases h : 0 ≤ torusCenteredRep x i - torusCenteredRep y i + 1
    · rw [abs_of_nonneg h]
      by_cases hax : 0 ≤ torusCenteredRep x i
      · by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hax, abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonneg hax, abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · rw [abs_of_nonpos (le_of_not_ge hax)]
        by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
    · have hneg : torusCenteredRep x i - torusCenteredRep y i + 1 < 0 :=
        lt_of_not_ge h
      rw [abs_of_neg hneg]
      by_cases hax : 0 ≤ torusCenteredRep x i
      · by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hax, abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonneg hax, abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · rw [abs_of_nonpos (le_of_not_ge hax)]
        by_cases hby : 0 ≤ torusCenteredRep y i
        · rw [abs_of_nonneg hby]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
        · rw [abs_of_nonpos (le_of_not_ge hby)]
          linarith [hn, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

theorem torusSpatialNorm_sub_le (x y : Torus3) :
    torusSpatialNorm (x - y) ≤
      2 * (torusSpatialNorm x + torusSpatialNorm y) := by
  let a := torusCenteredRep x
  let b := torusCenteredRep y
  let c := torusCenteredRep (x - y)
  let A := torusSpatialNorm x
  let B := torusSpatialNorm y
  let M := A + B
  have hA : 0 ≤ A := torusSpatialNorm_nonneg x
  have hB : 0 ≤ B := torusSpatialNorm_nonneg y
  have hM : 0 ≤ M := add_nonneg hA hB
  have hcoordA : ∀ i, |a i| ≤ A := by
    intro i
    apply (sq_le_sq₀ (abs_nonneg _) (by exact hA)).mp
    rw [sq_abs]
    dsimp [A]
    dsimp [a]
    rw [torusSpatialNorm_sq x]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  have hcoordB : ∀ i, |b i| ≤ B := by
    intro i
    apply (sq_le_sq₀ (abs_nonneg _) (by exact hB)).mp
    rw [sq_abs]
    dsimp [B]
    dsimp [b]
    rw [torusSpatialNorm_sq y]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
  have hcoord : ∀ i, |c i| ≤ M := by
    intro i
    exact (abs_torusCenteredRep_sub_le x y i).trans
      (add_le_add (hcoordA i) (hcoordB i))
  have hsum : sqNorm3 c ≤ 3 * M ^ 2 := by
    unfold sqNorm3
    calc
      ∑ i, c i ^ 2 ≤ ∑ _i : Fin 3, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sq_abs (c i)]
        exact (sq_le_sq₀ (abs_nonneg _) hM).2 (hcoord i)
      _ = 3 * M ^ 2 := by simp
  have hfinal : √(sqNorm3 c) ≤ 2 * M := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt]
    · nlinarith [hsum]
    · exact Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  simpa [torusSpatialNorm, c, M, A, B] using hfinal

theorem torusSpatialNorm_zero : torusSpatialNorm (0 : Torus3) = 0 := by
  have hrep : torusRep (0 : Torus3) = 0 := by
    funext i
    dsimp [torusRep]
    have h := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
      (x := (0 : ℝ)) (by norm_num : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1))
    exact congrArg Subtype.val h
  unfold torusSpatialNorm
  unfold torusCenteredRep
  rw [hrep]
  simp [sqNorm3]
  split_ifs with h
  · norm_num at h
  · norm_num

theorem torusSpatialNorm_le_seven_eighth (x : Torus3) :
    torusSpatialNorm x ≤ (7 : ℝ) / 8 := by
  apply (sq_le_sq₀ (torusSpatialNorm_nonneg x) (by norm_num)).mp
  rw [torusSpatialNorm_sq]
  have hsum : sqNorm3 (torusCenteredRep x) ≤ (3 : ℝ) / 4 := by
    unfold sqNorm3
    calc
      ∑ i, torusCenteredRep x i ^ 2 ≤ ∑ _i : Fin 3, ((1 : ℝ) / 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sq_abs]
        apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2
        exact (abs_le).2 (torusCenteredRep_mem_Icc x i)
      _ = (3 : ℝ) / 4 := by norm_num
  nlinarith [hsum]

theorem torusSpatialNorm_neg_le (x : Torus3) :
    torusSpatialNorm (-x) ≤ 2 * torusSpatialNorm x := by
  have h := torusSpatialNorm_sub_le (0 : Torus3) x
  simpa [sub_eq_add_neg, torusSpatialNorm_zero] using h

private theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a + b) ≤ √a + √b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem torusParabolicSize_sub_le (z w : SpaceTime) :
    torusParabolicSize z ≤ 4 *
      (torusParabolicSize (z - w) + torusParabolicSize w) := by
  have htime : √|z.1| ≤ √|z.1 - w.1| + √|w.1| := by
    have habs : |z.1| ≤ |z.1 - w.1| + |w.1| := by
      calc
        |z.1| = |z.1 - w.1 + w.1| := by congr 1; ring
        _ ≤ |z.1 - w.1| + |w.1| := abs_add_le (z.1 - w.1) w.1
    exact (sqrt_le_sqrt habs).trans
      (sqrt_add_le_sqrt_add_sqrt (abs_nonneg _) (abs_nonneg _))
  have hspace : torusSpatialNorm z.2 ≤
      2 * (torusSpatialNorm (z - w).2 + 2 * torusSpatialNorm w.2) := by
    have h := torusSpatialNorm_sub_le (z - w).2 (-w.2)
    have hn := torusSpatialNorm_neg_le w.2
    calc
      torusSpatialNorm z.2 =
          torusSpatialNorm ((z - w).2 - (-w.2)) := by
            congr 1
            simp [sub_eq_add_neg, add_comm]
      _ ≤ 2 * (torusSpatialNorm (z - w).2 + torusSpatialNorm (-w.2)) := h
      _ ≤ 2 * (torusSpatialNorm (z - w).2 + 2 * torusSpatialNorm w.2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (le_refl _) hn
  unfold torusParabolicSize
  calc
    √|z.1| + torusSpatialNorm z.2 ≤
        (√|z.1 - w.1| + √|w.1|) +
          2 * (torusSpatialNorm (z - w).2 + 2 * torusSpatialNorm w.2) :=
      add_le_add htime hspace
    _ ≤ 4 * ((√|z.1 - w.1| + torusSpatialNorm (z - w).2) +
        (√|w.1| + torusSpatialNorm w.2)) := by
      nlinarith [torusSpatialNorm_nonneg (z - w).2, torusSpatialNorm_nonneg w.2,
        Real.sqrt_nonneg |z.1 - w.1|, Real.sqrt_nonneg |w.1|]

end RegularityStructures

end
