/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Slice
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import RegularityStructures.Torus.KolmogorovHolderBesovHeat

/-!
# The massive potential as a Duhamel integral of the slices

If `ψ` is the massive potential of the continuous forcing `f` (`IsMassivePotential f ψ`), then
`ψ t = ∫_{r ≤ t} e^{-(t-r)} P_{t-r} f_r dr` in `C(T³)` (`potential_eq_integral_potF`): Fubini for
the product measure on `ℝ × T³` and `P_s f (x) = ∫ p_s(y) f(x - y) dy` (`heatSemigroup_eq_torus_integral`).
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Potential

open RegularityStructures

theorem potential_apply_eq {f : SpaceTime → ℝ} (hf : Continuous f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (t : ℝ) (x : Torus3) :
    ψ t x = ∫ r in Iio t, potF hf t r x := by
  have hint := hψ.1 t x
  rw [hψ.2 t x]
  have hp : (volume : Measure SpaceTime) = (volume : Measure ℝ).prod (volume : Measure Torus3) :=
    rfl
  rw [hp] at hint ⊢
  rw [integral_prod _ hint]
  rw [← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r < t
  · have hτ : 0 < t - r := by linarith
    rw [indicator_of_mem (show r ∈ Iio t from hr)]
    simp only [potF, ContinuousMap.smul_apply, smul_eq_mul]
    rw [PDE.heatOp_eq_heatSemigroup hτ, heatSemigroup_eq_torus_integral hτ, ← integral_const_mul]
    simp only [Prod.mk_sub_mk]
    rw [← integral_sub_left_eq_self (μ := (volume : Measure Torus3)) (fun y : Torus3 => massiveHeatKernel (t - r, x - y) * f (r, y)) x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel, massiveHeatKernel, hτ, ite_true]
    simp [potSlice_apply]
    ring
  · rw [indicator_of_notMem (show r ∉ Iio t from hr)]
    have : ∀ y : Torus3, massiveHeatKernel (t - r, x - y) = 0 := by
      intro y
      have : ¬ 0 < t - r := by linarith [not_lt.1 hr]
      simp [massiveHeatKernel, this]
    simp [this]

/-- **The massive potential is the Duhamel integral of the slices**, in `C(T³)`. -/
theorem potential_eq_integral_potF {f : SpaceTime → ℝ} (hF : PotForcing f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (t : ℝ) :
    ψ t = ∫ r in Iic t, potF hF.cont t r := by
  ext x
  have h := (ContinuousMap.evalCLM ℝ x).integral_comp_comm (integrableOn_potF hF t)
  have h2 : (∫ r in Iic t, potF hF.cont t r) x = ∫ r in Iic t, potF hF.cont t r x := h.symm
  rw [h2, integral_Iic_eq_integral_Iio]
  exact potential_apply_eq hF.cont hψ t x

end RegularityStructures.Potential

end
