module

public import GlobalPhi43.MW20.BarrierDerivatives
public import GlobalPhi43.MW20.CubicBarrierAlgebra
public import GlobalPhi43.MW20.HeatAlgebra

/-!
# The explicit reciprocal boundary barrier for the cubic equation
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Filter Topology

/-- Contribution of the two spatial faces of a coordinate interval. -/
@[expose] noncomputable def faceFactor (x : ℝ) : ℝ := (1 - x)⁻¹ + (1 + x)⁻¹

/-- Spatial reciprocal distance sum. -/
@[expose] noncomputable def faceSum (x : Fin 3 → ℝ) : ℝ := ∑ i, faceFactor (x i)

/-- Cubic boundary barrier with forcing bound `G³`. -/
@[expose] noncomputable def cubicBarrier (G : ℝ) (z : ParabolicSpace) : ℝ :=
  2 * (inverseRoot z.1 + faceSum z.2) + G

/-- Smoothness of a spatial face factor away from both faces. -/
theorem faceFactor_contDiffAt {x : ℝ} (hx : -1 < x ∧ x < 1) :
    ContDiffAt ℝ 2 faceFactor x := by
  have hm : 1 - x ≠ 0 := by linarith [hx.2]
  have hp : 1 + x ≠ 0 := by linarith [hx.1]
  unfold faceFactor
  exact ((contDiffAt_const.sub contDiffAt_id).inv hm).add
    ((contDiffAt_const.add contDiffAt_id).inv hp)

/-- The second derivative of a pair of reciprocal face factors. -/
theorem faceFactor_deriv_deriv {x : ℝ} (hx : -1 < x ∧ x < 1) :
    deriv (deriv faceFactor) x = 2 * ((1 - x)⁻¹ ^ 3 + (1 + x)⁻¹ ^ 3) := by
  have hm : 1 + (-1 : ℝ) * x ≠ 0 := by linarith [hx.2]
  have hp : 1 + (1 : ℝ) * x ≠ 0 := by linarith [hx.1]
  have hcm : ContDiffAt ℝ 2 (reciprocalAffine 1 (-1)) x := by
    unfold reciprocalAffine
    exact (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).inv hm
  have hcp : ContDiffAt ℝ 2 (reciprocalAffine 1 1) x := by
    unfold reciprocalAffine
    exact (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).inv hp
  have hsum := iteratedDeriv_fun_add hcm hcp
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hsum
  have heq : faceFactor = fun y => reciprocalAffine 1 (-1) y + reciprocalAffine 1 1 y := by
    funext y
    simp [faceFactor, reciprocalAffine, sub_eq_add_neg]
  rw [heq, hsum, reciprocalAffine_deriv_deriv 1 (-1) hm, reciprocalAffine_deriv_deriv 1 1 hp]
  simp only [neg_one_mul, one_mul, neg_sq, one_pow]
  simp only [sub_eq_add_neg, div_eq_mul_inv, inv_pow]
  ring

/-- Updating one coordinate splits its face contribution off from the other two. -/
theorem faceSum_update (x : Fin 3 → ℝ) (i : Fin 3) (y : ℝ) :
    faceSum (Function.update x i y) =
      (∑ j ∈ Finset.univ.erase i, faceFactor (x j)) + faceFactor y := by
  unfold faceSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.1 hj).1]
  · rw [Function.update_self]

/-- The spatial second derivative of the full barrier, on the interior. -/
theorem cubicBarrier_spatial_second (G : ℝ) (z : ParabolicSpace) (i : Fin 3)
    (hx : -1 < z.2 i ∧ z.2 i < 1) :
    deriv (deriv (fun y => cubicBarrier G (z.1, Function.update z.2 i y))) (z.2 i) =
      4 * ((1 - z.2 i)⁻¹ ^ 3 + (1 + z.2 i)⁻¹ ^ 3) := by
  have heq : (fun y => cubicBarrier G (z.1, Function.update z.2 i y)) =
      fun y => (2 * (inverseRoot z.1 + ∑ j ∈ Finset.univ.erase i, faceFactor (z.2 j)) + G) +
        2 * faceFactor y := by
    funext y
    rw [cubicBarrier, faceSum_update]
    ring
  have hd := iteratedDeriv_const_add (n := 2) (by omega)
    (f := fun y => 2 * faceFactor y) (x := z.2 i)
    (2 * (inverseRoot z.1 + ∑ j ∈ Finset.univ.erase i, faceFactor (z.2 j)) + G)
  rw [iteratedDeriv_const_mul_field] at hd
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd
  rw [heq, hd, faceFactor_deriv_deriv hx]
  ring

/-- Time derivative of the full barrier. -/
theorem cubicBarrier_time (G : ℝ) (z : ParabolicSpace) (ht : 0 < z.1) :
    HasDerivAt (fun t => cubicBarrier G (t, z.2)) (-(inverseRoot z.1) ^ 3) z.1 := by
  have hd := (((inverseRoot_hasDerivAt ht).add_const (faceSum z.2)).const_mul 2).add_const G
  convert! hd using 1
  ring

end GlobalPhi43.MW20
