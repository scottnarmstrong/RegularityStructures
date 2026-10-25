/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Lift
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Measurability and support of the Taylor lift

The derivatives `pdv v F` are measurable for every `F` (they are `0` for `t ≤ 0` and a derivative
of `F` otherwise), hence so are `D k F` and the lift `liftOf P γ₀ F`. If `F` vanishes on
`{t ≤ 0}` so does the lift.
-/

public section

open MeasureTheory

namespace RegularityStructures.Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

theorem measurable_pdv (v : ParabolicSpace) (F : ParabolicSpace → ℝ) : Measurable (pdv v F) := by
  unfold pdv
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (measurable_fderiv_apply_const ℝ F v) measurable_const

theorem measurable_pdIter {F : ParabolicSpace → ℝ} (hF : Measurable F) (i : Fin 4) (n : ℕ) :
    Measurable (pdIter i n F) := by
  induction n with
  | zero => exact hF
  | succ n ih => rw [pdIter_succ']; exact measurable_pdv _ _

theorem measurable_D {F : ParabolicSpace → ℝ} (hF : Measurable F) (k : Fin 4 → ℕ) :
    Measurable (D k F) :=
  measurable_pdIter (measurable_pdIter (measurable_pdIter (measurable_pdIter hF 3 _) 2 _) 1 _) 0 _

theorem measurable_liftCoeff {F : ParabolicSpace → ℝ} (hF : Measurable F) (γ₀ : ℝ)
    (k : PolyIndex N) : Measurable fun x => liftCoeff N γ₀ F x k := by
  unfold liftCoeff
  by_cases h : polyDeg N k < γ₀
  · simp only [h, ↓reduceIte]
    exact (measurable_D hF _).div_const _
  · simp only [h, ↓reduceIte]
    exact measurable_const

theorem measurable_liftOf (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {F : ParabolicSpace → ℝ}
    (hF : Measurable F) : Measurable (liftOf P γ₀ F) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold liftOf PolynomialSector.polyEmbed
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ => (measurable_liftCoeff hF γ₀ k).mul measurable_const

theorem measurable_of_smoothPos {F : ParabolicSpace → ℝ} (hF : SmoothPos F)
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → F z = 0) : Measurable F := by
  classical
  have hs : MeasurableSet posTime := measurableSet_lt measurable_const measurable_fst
  have e : F = posTime.piecewise F 0 := by
    funext z
    by_cases hz : z ∈ posTime
    · simp [hz]
    · simp [hz, h0 z (not_lt.1 hz)]
  rw [e]
  exact ContinuousOn.measurable_piecewise (hF.continuousOn) continuousOn_const hs

end RegularityStructures.Datum

end
