module

public import GlobalPhi43.MW20.BarrierRegularity
public import GlobalPhi43.MW20.CylinderSup

/-!
# Boundary domination on finite truncations of the source cylinder
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Nonnegativity of the full barrier inside the cylinder. -/
theorem cubicBarrier_nonneg {G : ℝ} (hG : 0 ≤ G) (z : ParabolicSpace)
    (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) : 0 ≤ cubicBarrier G z := by
  have htime : 0 ≤ inverseRoot z.1 := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hspace : 0 ≤ faceSum z.2 := Finset.sum_nonneg fun i _ => faceFactor_nonneg (hx i)
  unfold cubicBarrier
  positivity

/-- The barrier dominates twice the reciprocal time distance. -/
theorem cubicBarrier_ge_time {G : ℝ} (hG : 0 ≤ G) (z : ParabolicSpace)
    (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) : 2 * inverseRoot z.1 ≤ cubicBarrier G z := by
  have hspace : 0 ≤ faceSum z.2 := Finset.sum_nonneg fun i _ => faceFactor_nonneg (hx i)
  unfold cubicBarrier
  linarith

/-- The barrier dominates the reciprocal distance to each spatial face. -/
theorem cubicBarrier_ge_faces {G : ℝ} (hG : 0 ≤ G) (z : ParabolicSpace)
    (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) (i : Fin 3) :
    2 * (1 - z.2 i)⁻¹ ≤ cubicBarrier G z ∧
      2 * (1 + z.2 i)⁻¹ ≤ cubicBarrier G z := by
  have htime : 0 ≤ inverseRoot z.1 := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hf : faceFactor (z.2 i) ≤ faceSum z.2 :=
    Finset.single_le_sum (fun j _ => faceFactor_nonneg (hx j)) (Finset.mem_univ i)
  have hm : 0 ≤ (1 - z.2 i)⁻¹ := inv_nonneg.mpr (by linarith [(hx i).2])
  have hp : 0 ≤ (1 + z.2 i)⁻¹ := inv_nonneg.mpr (by linarith [(hx i).1])
  unfold faceFactor at hf
  unfold cubicBarrier
  constructor <;> linarith

/-- A truncated compact cylinder, with terminal time `T`. -/
@[expose] def truncatedCylinder (δ T : ℝ) : Set ParabolicSpace :=
  Icc (δ ^ 2, fun _ => -1 + δ) (T, fun _ => 1 - δ)

/-- Every point in the finite truncation is in the original open spatial box
and at a strictly positive time. -/
theorem truncatedCylinder_interior {δ T : ℝ} (hδ : 0 < δ) {z : ParabolicSpace}
    (hz : z ∈ truncatedCylinder δ T) : 0 < z.1 ∧ ∀ i, -1 < z.2 i ∧ z.2 i < 1 := by
  refine ⟨(sq_pos_of_pos hδ).trans_le hz.1.1, ?_⟩
  intro i
  constructor <;> linarith [hz.1.2 i, hz.2.2 i]

/-- The explicit barrier dominates the same reciprocal inset on every
parabolic boundary face of a finite truncation. -/
theorem cubicBarrier_ge_boundary {δ T G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    {z : ParabolicSpace} (hz : z ∈ truncatedCylinder δ T)
    (hbd : z.1 = δ ^ 2 ∨ ∃ i, z.2 i = -1 + δ ∨ z.2 i = 1 - δ) :
    2 / δ ≤ cubicBarrier G z := by
  have hi := truncatedCylinder_interior hδ hz
  rcases hbd with ht | ⟨i, hm | hp⟩
  · have hb := cubicBarrier_ge_time hG z hi.2
    simpa only [ht, inverseRoot, Real.sqrt_sq hδ.le, div_eq_mul_inv] using hb
  · have hb := (cubicBarrier_ge_faces hG z hi.2 i).2
    have he : 1 + z.2 i = δ := by rw [hm]; ring
    simpa only [he, div_eq_mul_inv] using hb
  · have hb := (cubicBarrier_ge_faces hG z hi.2 i).1
    have he : 1 - z.2 i = δ := by rw [hp]; ring
    simpa only [he, div_eq_mul_inv] using hb

/-- Select a positive inset compatible with an evaluation depth and any
finite boundary bound. The estimate constant is unaffected by this choice. -/
theorem exists_barrier_inset (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > 0, δ ≤ ρ ∧ M ≤ 2 / δ := by
  let δ := min ρ (1 / (|M| + 1))
  have hden : 0 < |M| + 1 := by positivity
  have hδ : 0 < δ := lt_min hρ (one_div_pos.mpr hden)
  refine ⟨δ, hδ, min_le_left _ _, (le_div_iff₀ hδ).2 ?_⟩
  have hsmall : δ * (|M| + 1) ≤ 1 := (le_div_iff₀ hden).1 (min_le_right _ _)
  have hM := le_abs_self M
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hM)]

end GlobalPhi43.MW20
