module

public import GlobalPhi43.MW20.LocalMaximum
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Coordinate heat-operator algebra for the local comparison proof
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The coordinate heat operator respects subtraction whenever the time
sections are differentiable and the spatial sections are twice differentiable. -/
theorem sourceHeat_sub {u v : ParabolicSpace → ℝ} (z : ParabolicSpace)
    (hut : DifferentiableAt ℝ (fun t => u (t, z.2)) z.1)
    (hvt : DifferentiableAt ℝ (fun t => v (t, z.2)) z.1)
    (hux : ∀ i, ContDiffAt ℝ 2 (fun x => u (z.1, Function.update z.2 i x)) (z.2 i))
    (hvx : ∀ i, ContDiffAt ℝ 2 (fun x => v (z.1, Function.update z.2 i x)) (z.2 i)) :
    sourceHeat (fun y => u y - v y) z = sourceHeat u z - sourceHeat v z := by
  have hsecond (i : Fin 3) :
      deriv (deriv (fun x => u (z.1, Function.update z.2 i x) -
        v (z.1, Function.update z.2 i x))) (z.2 i) =
      deriv (deriv (fun x => u (z.1, Function.update z.2 i x))) (z.2 i) -
        deriv (deriv (fun x => v (z.1, Function.update z.2 i x))) (z.2 i) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      iteratedDeriv_fun_sub (hux i) (hvx i)
  unfold sourceHeat
  rw [deriv_fun_sub hut hvt]
  simp_rw [hsecond]
  rw [Finset.sum_sub_distrib]
  ring

end GlobalPhi43.MW20
