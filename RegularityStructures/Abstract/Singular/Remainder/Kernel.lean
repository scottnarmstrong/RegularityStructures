/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Cell
public import RegularityStructures.Abstract.Singular.Remainder.Weight
public import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant

/-!
# Remainder kernels and their cell pieces

A *remainder kernel* with constant `B` is a smooth `Φ : ℝ⁴ → ℝ` whose derivatives of order `≤ 4`
satisfy `‖D^i Φ(u)‖ ≤ B (1 + |u'|²)^{-3}` for `u₀ ≤ 3` (`IsRemKernel`).  The test function
`y ↦ Φ(x − y)` is then cut into the level-3 cells; each piece `Φ(x − ·) χ_{3,j}` is supported in
`B(z_j, 1)` with scaled derivatives `≲ B (1 + |x' − z_j'|²)^{-3}`, uniformly in `x` with `x₀ ≤ 1`
and `j₀ ≥ -1` (`scaled_bound_remPiece`).
-/

@[expose] public section

namespace RegularityStructures

/-- A smooth function with decaying derivatives (orders `≤ 4`, times `≤ 3`) with constant `B`. -/
structure IsRemKernel (Φ : ParabolicSpace → ℝ) (B : ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) Φ
  nonneg : 0 ≤ B
  decay : RemDecay Φ 4 3 B

end RegularityStructures

end

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem norm_iteratedFDeriv_comp_const_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (a v : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun v => f (a - v)) v‖ = ‖iteratedFDeriv ℝ i f (a - v)‖ := by
  have e : (fun v => f (a - v)) = (fun u => f (a + u)) ∘ (LinearIsometryEquiv.neg ℝ) := by
    funext v; simp [sub_eq_add_neg]
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_left]
  simp [sub_eq_add_neg]

theorem abs_le_one_of_parabolicNorm_le_one {v : ParabolicSpace} (hv : parabolicNorm v ≤ 1) :
    |v.1| ≤ 1 ∧ ∀ i, |v.2 i| ≤ 1 := by
  have h := norm_le_one_of_parabolicNorm_le_one hv
  refine ⟨?_, fun i => ?_⟩
  · rw [← Real.norm_eq_abs]; exact (norm_fst_le v).trans h
  · rw [← Real.norm_eq_abs]; exact ((norm_le_pi_norm v.2 i).trans (norm_snd_le v)).trans h

/-- The scaled derivatives of the kernel `y ↦ Φ(x − y)` on the unit ball around `z_j`. -/
theorem scaled_bound_remPiece {Φ : ParabolicSpace → ℝ} {B : ℝ} (hΦ : IsRemKernel Φ B)
    {x : ParabolicSpace} {T : ℝ} (hT : T ≤ 1) (hx : x.1 ≤ T) {j : LatticeIndex}
    (hj : (-1 : ℤ) ≤ j.1) :
    ∀ i ≤ 4, ∀ v : ParabolicSpace, parabolicNorm v ≤ 1 →
      ‖iteratedFDeriv ℝ i (fun v => (fun y => Φ (x - y)) (latticePoint 3 j + v)) v‖ ≤
        (2 + 6 * (1 : ℝ) ^ 2) ^ 3 * B * remWt (x.2 - (latticePoint 3 j).2) := by
  intro i hi v hv
  have e : (fun v => (fun y => Φ (x - y)) (latticePoint 3 j + v)) =
      fun v => Φ ((x - latticePoint 3 j) - v) := by
    funext v; simp only [sub_add_eq_sub_sub]
  rw [e, norm_iteratedFDeriv_comp_const_sub]
  obtain ⟨hv1, hv2⟩ := abs_le_one_of_parabolicNorm_le_one hv
  have hz : (-1 : ℝ) / 64 ≤ (latticePoint 3 j).1 := by
    rw [latticePoint_fst]
    have : (-1 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hj
    nlinarith
  have hu : ((x - latticePoint 3 j) - v).1 ≤ 3 := by
    simp only [Prod.fst_sub]
    have := (abs_le.1 hv1).1
    linarith
  have h1 := hΦ.decay i (by omega) _ hu
  refine h1.trans ?_
  have hwt : remWt ((x - latticePoint 3 j) - v).2 ≤ (2 + 6 * (1 : ℝ) ^ 2) ^ 3 *
      remWt (x.2 - (latticePoint 3 j).2) :=
    remWt_le_mul_remWt (fun k => by
      simp only [Prod.snd_sub, Pi.sub_apply]
      rw [show x.2 k - (latticePoint 3 j).2 k - (x.2 k - (latticePoint 3 j).2 k - v.2 k) = v.2 k
        by ring]
      exact hv2 k)
  calc B * remWt ((x - latticePoint 3 j) - v).2
      ≤ B * ((2 + 6 * (1 : ℝ) ^ 2) ^ 3 * remWt (x.2 - (latticePoint 3 j).2)) :=
        mul_le_mul_of_nonneg_left hwt hΦ.nonneg
    _ = _ := by ring

end RegularityStructures

end
