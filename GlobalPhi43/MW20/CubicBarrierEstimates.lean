module

public import GlobalPhi43.MW20.CubicBarrier

/-!
# Supersolution and boundary-distance estimates for the cubic barrier
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The sum of the cubes of the reciprocal spatial face distances. -/
@[expose] noncomputable def faceCubeSum (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ((1 - x i)⁻¹ ^ 3 + (1 + x i)⁻¹ ^ 3)

/-- Nonnegativity of each spatial barrier contribution. -/
theorem faceFactor_nonneg {x : ℝ} (hx : -1 < x ∧ x < 1) : 0 ≤ faceFactor x := by
  unfold faceFactor
  exact add_nonneg (inv_nonneg.mpr (by linarith [hx.2]))
    (inv_nonneg.mpr (by linarith [hx.1]))

/-- The spatial face cubes are dominated by the cube of their sum. -/
theorem faceCubeSum_le (x : Fin 3 → ℝ) (hx : ∀ i, -1 < x i ∧ x i < 1) :
    faceCubeSum x ≤ faceSum x ^ 3 := by
  have hsmall : faceCubeSum x ≤ ∑ i, faceFactor (x i) ^ 3 := by
    apply Finset.sum_le_sum
    intro i _
    exact cube_add_ge (inv_nonneg.mpr (by linarith [(hx i).2]))
      (inv_nonneg.mpr (by linarith [(hx i).1]))
  exact hsmall.trans (sum_cube_le_cube_sum Finset.univ (fun i => faceFactor (x i))
    (fun i _ => faceFactor_nonneg (hx i)))

/-- The explicit heat operator of the reciprocal boundary barrier. -/
theorem sourceHeat_cubicBarrier (G : ℝ) (z : ParabolicSpace)
    (ht : 0 < z.1) (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) :
    sourceHeat (cubicBarrier G) z = -(inverseRoot z.1) ^ 3 - 4 * faceCubeSum z.2 := by
  unfold sourceHeat
  rw [(cubicBarrier_time G z ht).deriv]
  simp_rw [cubicBarrier_spatial_second G z _ (hx _)]
  rw [← Finset.mul_sum]
  rfl

/-- The cubic barrier is a supersolution for forcing bounded above by `G³`. -/
theorem cubicBarrier_supersolution (G : ℝ) (hG : 0 ≤ G) (z : ParabolicSpace)
    (ht : 0 < z.1) (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) :
    G ^ 3 - cubicBarrier G z ^ 3 ≤ sourceHeat (cubicBarrier G) z := by
  have hq : 0 ≤ inverseRoot z.1 := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hS : 0 ≤ faceSum z.2 := Finset.sum_nonneg fun i _ => faceFactor_nonneg (hx i)
  have hH : 0 ≤ faceCubeSum z.2 := by
    apply Finset.sum_nonneg
    intro i _
    exact add_nonneg (pow_nonneg (inv_nonneg.mpr (by linarith [(hx i).2])) _)
      (pow_nonneg (inv_nonneg.mpr (by linarith [(hx i).1])) _)
  have hb := cubic_barrier_supersolution hq hS hH hG (faceCubeSum_le z.2 hx)
  rw [sourceHeat_cubicBarrier G z ht hx]
  unfold cubicBarrier
  linarith

/-- The reciprocal barrier has the required inverse-distance growth, with a
universal constant. `ρ² ≤ t` and `ρ ≤ 1±x_i` express parabolic boundary depth. -/
theorem cubicBarrier_le_boundary (G : ℝ) (z : ParabolicSpace) {ρ : ℝ}
    (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) :
    cubicBarrier G z ≤ 15 * max (1 / ρ) G := by
  have htime : inverseRoot z.1 ≤ 1 / ρ := by
    simpa only [inverseRoot, one_div] using
      one_div_le_one_div_of_le hρ (Real.le_sqrt_of_sq_le ht)
  have hface : faceSum z.2 ≤ 6 / ρ := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      add_le_add (one_div_le_one_div_of_le hρ (hx i).1)
        (one_div_le_one_div_of_le hρ (hx i).2))
    have heq : 6 / ρ = (3 : ℝ) * ρ⁻¹ + 3 * ρ⁻¹ := by ring
    rw [heq]
    simpa [faceSum, faceFactor, one_div, Fin.sum_univ_succ] using hsum
  have hmax1 := le_max_left (1 / ρ) G
  have hmax2 := le_max_right (1 / ρ) G
  unfold cubicBarrier
  simp only [div_eq_mul_inv, one_mul] at htime hface hmax1
  simp only [one_div] at *
  linarith

end GlobalPhi43.MW20
