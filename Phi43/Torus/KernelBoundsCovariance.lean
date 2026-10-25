/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsMollified
public import RegularityStructures.Torus.HeatKernelIntegral

/-!
# Parabolic volume and covariance bounds

The covariance estimate uses the homogeneous dimension five of space-time.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric

namespace RegularityStructures

namespace Phi43

theorem torusSpatialNorm_coord_le (x : Torus3) (r : ℝ)
    (hx : torusSpatialNorm x ≤ r) (i : Fin 3) :
    |torusCenteredRep x i| ≤ r := by
  apply (sq_le_sq₀ (abs_nonneg _) (by linarith [torusSpatialNorm_nonneg x])).mp
  rw [sq_abs]
  calc
    torusCenteredRep x i ^ 2 ≤ sqNorm3 (torusCenteredRep x) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (torusCenteredRep x j))
        (Finset.mem_univ i)
    _ = torusSpatialNorm x ^ 2 := (torusSpatialNorm_sq x).symm
    _ ≤ r ^ 2 := (sq_le_sq₀ (torusSpatialNorm_nonneg x)
      (by linarith [torusSpatialNorm_nonneg x])).2 hx

theorem torusSpatialNorm_coord_dist_le (x : Torus3) (r : ℝ)
    (hx : torusSpatialNorm x ≤ r) (i : Fin 3) :
    dist (x i) 0 ≤ r := by
  have hxi : x i = ((torusCenteredRep x i : ℝ) : UnitAddCircle) := by
    exact congrFun (torusProj_torusCenteredRep x) i |>.symm
  have hi := torusCenteredRep_mem_Icc x i
  have hi' : torusCenteredRep x i ∈ Icc (-(abs (1 : ℝ) / 2)) (abs (1 : ℝ) / 2) := by
    simpa using hi
  have hnorm :
      ‖((torusCenteredRep x i : ℝ) : UnitAddCircle)‖ = |torusCenteredRep x i| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ))
      (by norm_num : (1 : ℝ) ≠ 0)).2 (by
        exact (abs_le).2 hi')
  rw [hxi, dist_eq_norm, sub_zero, hnorm]
  exact torusSpatialNorm_coord_le x r hx i

theorem volume_torusSpatialBall_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    volume {x : Torus3 | torusSpatialNorm x ≤ r} ≤ ENNReal.ofReal (8 * r ^ 3) := by
  let S : Set Torus3 := {x | torusSpatialNorm x ≤ r}
  let T : Set Torus3 :=
    Set.pi Set.univ (fun _ : Fin 3 => Metric.closedBall (0 : UnitAddCircle) r)
  have hST : S ⊆ T := by
    intro x hx i hi
    exact (mem_closedBall).2 (torusSpatialNorm_coord_dist_le x r hx i)
  have hT : volume T =
      ∏ _i : Fin 3, volume (Metric.closedBall (0 : UnitAddCircle) r) := by
    dsimp [T]
    rw [volume_pi_pi]
  have hcircle :
      volume (Metric.closedBall (0 : UnitAddCircle) r) = ENNReal.ofReal (2 * r) := by
    rw [AddCircle.volume_closedBall]
    congr 1
    rw [min_eq_right]
    linarith
  calc
    volume S ≤ volume T := measure_mono hST
    _ = ∏ _i : Fin 3, volume (Metric.closedBall (0 : UnitAddCircle) r) := hT
    _ = ENNReal.ofReal (8 * r ^ 3) := by
      rw [hcircle]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.ofReal_pow]
      · congr 1
        ring
      · positivity

theorem volume_torusParabolicBall_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤ ENNReal.ofReal (16 * r ^ 5) := by
  let S : Set SpaceTime := {z | torusParabolicSize z ≤ r}
  let T : Set SpaceTime :=
    Icc (-(r ^ 2)) (r ^ 2) ×ˢ {x : Torus3 | torusSpatialNorm x ≤ r}
  have hST : S ⊆ T := by
    intro z hz
    change torusParabolicSize z ≤ r at hz
    constructor
    · have htime : √|z.1| ≤ r := by
        unfold torusParabolicSize at hz
        linarith [torusSpatialNorm_nonneg z.2]
      have hsquare : (√|z.1|) ^ 2 = |z.1| := Real.sq_sqrt (abs_nonneg _)
      have hsq : |z.1| ≤ r ^ 2 := by
        nlinarith [hsquare, Real.sqrt_nonneg |z.1|]
      rw [mem_Icc]
      exact abs_le.mp hsq
    · change torusSpatialNorm z.2 ≤ r
      exact (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hz
  have hT : volume T =
      volume (Icc (-(r ^ 2)) (r ^ 2)) *
        volume {x : Torus3 | torusSpatialNorm x ≤ r} := by
    dsimp [T]
    change ((volume : Measure ℝ).prod (volume : Measure Torus3))
      (Icc (-(r ^ 2)) (r ^ 2) ×ˢ {x : Torus3 | torusSpatialNorm x ≤ r}) = _
    rw [Measure.prod_prod]
  calc
    volume S ≤ volume T := measure_mono hST
    _ = volume (Icc (-(r ^ 2)) (r ^ 2)) *
        volume {x : Torus3 | torusSpatialNorm x ≤ r} := hT
    _ ≤ ENNReal.ofReal (2 * r ^ 2) * ENNReal.ofReal (8 * r ^ 3) := by
      have hvol : volume (Icc (-(r ^ 2)) (r ^ 2)) =
          ENNReal.ofReal (2 * r ^ 2) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      rw [hvol]
      gcongr
      exact volume_torusSpatialBall_le hr hr1
    _ = ENNReal.ofReal (16 * r ^ 5) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * r ^ 2)]
      congr 1
      ring_nf

theorem measurable_torusParabolicSize : Measurable torusParabolicSize := by
  have hrep : Measurable torusRep := measurable_torusRep
  have hcenter : ∀ i : Fin 3,
      Measurable (fun x : Torus3 => torusCenteredRep x i) := by
    intro i
    have hi : Measurable (fun x : Torus3 => torusRep x i) :=
      (measurable_pi_apply i).comp hrep
    exact Measurable.ite (measurableSet_Ici.preimage hi)
      (hi.sub measurable_const) hi
  have hsq : Measurable (fun x : Torus3 => sqNorm3 (torusCenteredRep x)) := by
    unfold sqNorm3
    exact Finset.measurable_fun_sum Finset.univ fun i _ => (hcenter i).pow_const 2
  have hsp : Measurable torusSpatialNorm := hsq.sqrt
  have ht : Measurable (fun z : SpaceTime => √|z.1|) :=
    by
      have heq : (fun z : SpaceTime => √|z.1|) =
          (fun z : SpaceTime => √‖z.1‖) := by
        funext z
        simp only [Real.norm_eq_abs]
      rw [heq]
      exact (measurable_fst.norm).sqrt
  exact ht.add (hsp.comp measurable_snd)

theorem volume_torusParabolicBall_le_global {r : ℝ} (hr : 0 ≤ r) :
    volume {z : SpaceTime | torusParabolicSize z ≤ r} ≤ ENNReal.ofReal (16 * r ^ 5) := by
  by_cases hr1 : r ≤ 1 / 2
  · exact volume_torusParabolicBall_le hr hr1
  · let S : Set SpaceTime := {z | torusParabolicSize z ≤ r}
    let T : Set SpaceTime := Icc (-(r ^ 2)) (r ^ 2) ×ˢ (Set.univ : Set Torus3)
    have hST : S ⊆ T := by
      intro z hz
      change torusParabolicSize z ≤ r at hz
      have htime : √|z.1| ≤ r := by
        unfold torusParabolicSize at hz
        linarith [torusSpatialNorm_nonneg z.2]
      have hsquare : (√|z.1|) ^ 2 = |z.1| := Real.sq_sqrt (abs_nonneg _)
      have hsq : |z.1| ≤ r ^ 2 := by
        nlinarith [hsquare, Real.sqrt_nonneg |z.1|]
      exact ⟨abs_le.mp hsq, Set.mem_univ _⟩
    have hT : volume T = ENNReal.ofReal (2 * r ^ 2) := by
      dsimp [T]
      change ((volume : Measure ℝ).prod (volume : Measure Torus3))
        (Icc (-(r ^ 2)) (r ^ 2) ×ˢ (Set.univ : Set Torus3)) = _
      have hIcc : volume (Icc (-(r ^ 2)) (r ^ 2)) =
          ENNReal.ofReal (2 * r ^ 2) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      rw [Measure.prod_prod, hIcc]
      rw [show (Set.univ : Set Torus3) = Set.pi Set.univ (fun _ => Set.univ) by
        ext x
        simp]
      rw [volume_pi_pi]
      simp
    calc
      volume S ≤ volume T := measure_mono hST
      _ = ENNReal.ofReal (2 * r ^ 2) := hT
      _ ≤ ENNReal.ofReal (16 * r ^ 5) := by
        apply ENNReal.ofReal_le_ofReal
        have hrhalf : (1 : ℝ) / 2 ≤ r := le_of_not_ge hr1
        have hpow : ((1 : ℝ) / 2) ^ (3 : ℕ) ≤ r ^ (3 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) hrhalf 3
        have hnonneg : 0 ≤ r ^ 2 * (16 * r ^ 3 - 2) := by
          apply mul_nonneg (sq_nonneg r)
          nlinarith [hpow]
        nlinarith [hnonneg]

end Phi43

end RegularityStructures

end
