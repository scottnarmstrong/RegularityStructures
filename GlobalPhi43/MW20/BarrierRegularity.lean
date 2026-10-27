module

public import GlobalPhi43.MW20.CubicBarrierEstimates

/-!
# Local smoothness of the cubic comparison barrier
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The barrier is twice continuously differentiable at every interior point,
including points with terminal time one. -/
theorem cubicBarrier_contDiffAt (G : ℝ) (z : ParabolicSpace)
    (ht : 0 < z.1) (hx : ∀ i, -1 < z.2 i ∧ z.2 i < 1) :
    ContDiffAt ℝ 2 (cubicBarrier G) z := by
  have htime : ContDiffAt ℝ 2 (fun y : ParabolicSpace => inverseRoot y.1) z := by
    unfold inverseRoot
    exact (contDiffAt_fst.sqrt ht.ne').inv (ne_of_gt (Real.sqrt_pos.2 ht))
  have hspace : ContDiffAt ℝ 2 (fun y : ParabolicSpace => faceSum y.2) z := by
    unfold faceSum
    apply ContDiffAt.sum
    intro i _
    have hi : ContDiffAt ℝ 2 (fun y : ParabolicSpace => y.2 i) z := by fun_prop
    exact (faceFactor_contDiffAt (hx i)).comp z hi
  exact (contDiffAt_const.mul (htime.add hspace)).add contDiffAt_const

/-- Restriction of a C² function to a time section is differentiable. -/
theorem time_differentiable_of_contDiffAt {w : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hw : ContDiffAt ℝ 2 w z) : DifferentiableAt ℝ (fun t => w (t, z.2)) z.1 := by
  have hpath : ContDiffAt ℝ 2 (fun t : ℝ => (t, z.2)) z.1 := by fun_prop
  exact (hw.comp z.1 hpath).differentiableAt (by norm_num)

/-- Restriction to a spatial coordinate section retains C² regularity. -/
theorem spatial_contDiffAt_of_contDiffAt {w : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hw : ContDiffAt ℝ 2 w z) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun x => w (z.1, Function.update z.2 i x)) (z.2 i) := by
  have hup : ContDiffAt ℝ 2 (fun x : ℝ => Function.update z.2 i x) (z.2 i) := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simpa using! (contDiffAt_id : ContDiffAt ℝ 2 (fun x : ℝ => x) (z.2 i))
    · simpa [Function.update_of_ne hj] using
        (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => z.2 j) (z.2 i))
  have hpath : ContDiffAt ℝ 2 (fun x : ℝ => (z.1, Function.update z.2 i x)) (z.2 i) :=
    contDiffAt_const.prodMk hup
  apply ContDiffAt.comp (z.2 i) _ hpath
  simpa using hw

/-- Subtraction identity for the local heat operator on C² germs. -/
theorem sourceHeat_sub_of_contDiffAt {u v : ParabolicSpace → ℝ} (z : ParabolicSpace)
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    sourceHeat (fun y => u y - v y) z = sourceHeat u z - sourceHeat v z :=
  sourceHeat_sub z (time_differentiable_of_contDiffAt hu) (time_differentiable_of_contDiffAt hv)
    (spatial_contDiffAt_of_contDiffAt hu) (spatial_contDiffAt_of_contDiffAt hv)

end GlobalPhi43.MW20
