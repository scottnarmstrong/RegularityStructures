/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.PDE.TorusLift
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Lifts of torus points and the parabolic size

Elementary facts about the centred lift `torusCenteredRep` used to turn increments of
periodised kernels on `ℝ × T³` into increments of the underlying kernels on `ℝ × ℝ³`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- A spatial periodisation does not depend on the chosen lift of the torus point. -/
theorem constantsRate_tsum_lift (F : (Fin 3 → ℝ) → ℝ) (x : Torus3) (y : Fin 3 → ℝ)
    (hy : torusProj y = x) :
    ∑' k : Fin 3 → ℤ, F (torusRep x + fun i => (k i : ℝ)) =
      ∑' k : Fin 3 → ℤ, F (y + fun i => (k i : ℝ)) := by
  have hcoord : ∀ i, ∃ m : ℤ, y i = torusRep x i + (m : ℝ) := by
    intro i
    have hi : ((torusRep x i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) := by
      have h1 : ((torusRep x i : ℝ) : UnitAddCircle) = x i := by
        dsimp [torusRep]
        exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := (x i : UnitAddCircle))
      rw [h1, ← hy]
      rfl
    have himem : torusRep x i - y i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    rcases AddSubgroup.mem_zmultiples_iff.mp himem with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have hm' : (m : ℝ) = torusRep x i - y i := by simpa using hm
    rw [Int.cast_neg]
    linarith
  choose m hm using hcoord
  have hym : y = torusRep x + fun i => (m i : ℝ) := by
    funext i
    exact hm i
  have : ∀ k : Fin 3 → ℤ, y + (fun i => (k i : ℝ)) =
      torusRep x + fun i => ((m + k) i : ℝ) := by
    intro k
    rw [hym]
    funext i
    simp only [Pi.add_apply, Int.cast_add]
    ring
  simp_rw [this]
  exact ((Equiv.addLeft m).tsum_eq
    (fun k : Fin 3 → ℤ => F (torusRep x + fun i => (k i : ℝ)))).symm

/-- The centred lift minimises the Euclidean norm over all lifts. -/
theorem constantsRate_spatialNorm_le_lift (x : Torus3) (k : Fin 3 → ℤ) :
    torusSpatialNorm x ≤ ∑ i, |torusCenteredRep x i + (k i : ℝ)| := by
  have hcoord : ∀ i : Fin 3,
      (torusCenteredRep x i) ^ 2 ≤ (torusCenteredRep x i + (k i : ℝ)) ^ 2 :=
    fun i => sq_centered_add_int_ge (torusCenteredRep_mem_Icc x i) (k i)
  have hsum : sqNorm3 (torusCenteredRep x) ≤
      sqNorm3 (torusCenteredRep x + fun i => (k i : ℝ)) := by
    unfold sqNorm3
    exact Finset.sum_le_sum fun i _ => hcoord i
  have hroot : √(sqNorm3 (torusCenteredRep x + fun i => (k i : ℝ))) ≤
      ∑ i, |torusCenteredRep x i + (k i : ℝ)| := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold sqNorm3
    simpa only [Pi.add_apply, sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin 3 => |torusCenteredRep x i + (k i : ℝ)|)
        (fun i _ => abs_nonneg _))
  unfold torusSpatialNorm
  exact (Real.sqrt_le_sqrt hsum).trans hroot

theorem constantsRate_size_le_centered_lift (z : SpaceTime) (k : Fin 3 → ℤ) :
    torusParabolicSize z ≤
      parabolicNorm (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) := by
  unfold torusParabolicSize parabolicNorm
  exact add_le_add le_rfl (constantsRate_spatialNorm_le_lift z.2 k)

/-- The `ℓ¹`-parabolic norm of the centred lift is controlled by the torus size. -/
theorem constantsRate_parabolicNorm_centered_le (h : SpaceTime) :
    parabolicNorm (h.1, torusCenteredRep h.2) ≤ 2 * torusParabolicSize h := by
  unfold parabolicNorm torusParabolicSize
  have hsq : (∑ i, |torusCenteredRep h.2 i|) ^ 2 ≤ 3 * sqNorm3 (torusCenteredRep h.2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun _ => (1 : ℝ)) (fun i => |torusCenteredRep h.2 i|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq_abs] at this
    unfold sqNorm3
    norm_num at this ⊢
    linarith
  have hS : ∑ i, |torusCenteredRep h.2 i| ≤ 2 * torusSpatialNorm h.2 := by
    have h0 : 0 ≤ ∑ i, |torusCenteredRep h.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h1 : (∑ i, |torusCenteredRep h.2 i|) ^ 2 ≤ (2 * torusSpatialNorm h.2) ^ 2 := by
      calc
        (∑ i, |torusCenteredRep h.2 i|) ^ 2 ≤ 3 * sqNorm3 (torusCenteredRep h.2) := hsq
        _ ≤ 4 * sqNorm3 (torusCenteredRep h.2) := by
          have : 0 ≤ sqNorm3 (torusCenteredRep h.2) := Finset.sum_nonneg fun i _ => sq_nonneg _
          linarith
        _ = (2 * torusSpatialNorm h.2) ^ 2 := by
          rw [mul_pow, torusSpatialNorm_sq]
          norm_num
    exact (sq_le_sq₀ h0 (mul_nonneg (by norm_num) (torusSpatialNorm_nonneg _))).mp h1
  have := Real.sqrt_nonneg |h.1|
  linarith

end RegularityStructures.Phi43

end
