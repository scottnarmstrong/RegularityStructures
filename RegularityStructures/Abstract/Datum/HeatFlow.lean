/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.HeatSmooth
public import RegularityStructures.PDE.MildSmooth

/-!
# The free heat flow of smooth data

For smooth `w ∈ C(T³)`, `t ↦ P_t w` is the mild solution of `∂_t u = Δu` with `G = 0`, so the
results of `RegularityStructures.PDE.MildSmooth` and `RegularityStructures.PDE.MildTime` apply:
`(t, y) ↦ P_t w (y)` is `C^∞` on `(0, ∞) × ℝ³` (`contDiffOn_heatFlow`) and `∂_t P_t w = Δ P_t w`
(`heatFlow_deriv`).
-/

open scoped ContDiff

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem isMildSolution_heatOp (w : C(Torus3, ℝ)) (T : ℝ) :
    IsMildSolution (0 : C(ℝ × Torus3 × ℝ, ℝ)) w T (fun t => heatOp t w) := by
  intro t _
  have h : (fun s => nemytskii (0 : C(ℝ × Torus3 × ℝ, ℝ)) s (heatOp s w)) =
      fun _ => (0 : C(Torus3, ℝ)) := by
    funext s
    ext x
    simp
  rw [h]
  simp [duhamel, heatOp_zero_right]

theorem contDiff_nonlinLift_zero : ContDiff ℝ ∞ (nonlinLift (0 : C(ℝ × Torus3 × ℝ, ℝ))) := by
  have : nonlinLift (0 : C(ℝ × Torus3 × ℝ, ℝ)) = fun _ => 0 := rfl
  rw [this]
  exact contDiff_const

/-- `(t, y) ↦ P_t w (y)` is `C^∞` on `(0, T) × ℝ³` for smooth `w`. -/
theorem contDiffOn_heatFlow {w : C(Torus3, ℝ)} (hw : ContDiff ℝ ∞ (liftFn w)) {T : ℝ}
    (hT : 0 ≤ T) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => heatOp p.1 w (torusProj p.2))
      (Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ))) :=
  contDiffOn_of_isMildSolution contDiff_nonlinLift_zero hw hT
    (continuous_heatOp_left w) (isMildSolution_heatOp w T)

/-- The time derivative of the heat flow of smooth data is the Laplacian. -/
theorem heatFlow_deriv {w : C(Torus3, ℝ)} (hw : ContDiff ℝ ∞ (liftFn w)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (w₁ : ℝ → C(Torus3, Fin 3 → ℝ)) (w₂ : ℝ → C(Torus3, Fin 3 → Fin 3 → ℝ)),
      (∀ t ∈ Icc 0 T, HasTorusDeriv (heatOp t w) (w₁ t)) ∧
      (∀ t ∈ Icc 0 T, HasTorusDeriv (E := Fin 3 → ℝ) (w₁ t) (w₂ t)) ∧
      ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => heatOp s w x) (torusLap (w₂ t) x) t := by
  obtain ⟨w₁, w₂, -, -, h1, h2, h3⟩ := hasDerivAt_of_isMildSolution contDiff_nonlinLift_zero hw hT
    (continuous_heatOp_left w) (isMildSolution_heatOp w T)
  refine ⟨w₁, w₂, h1, h2, fun t ht x => ?_⟩
  simpa using h3 t ht x

end RegularityStructures.Datum

end
