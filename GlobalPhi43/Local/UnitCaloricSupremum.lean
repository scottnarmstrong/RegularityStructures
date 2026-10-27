/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCaloricAllRadii
public import GlobalPhi43.MW20.ScalarSupNorm

/-! The unit heat-affine estimate with the literal extended-valued affine
error and source-heat supremum. No finiteness is an input hypothesis. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff ENNReal

 theorem exists_unit_caloric_supremum : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ R : ℝ, 0 ≤ R → R ≤ 1 →
        pastAffineError h 0 R ≤
          ENNReal.ofReal (C * R ^ 2) * pastAffineError h 0 1 +
            ENNReal.ofReal C * localScalarSup (sourceHeat h) (pastBall 0 1) := by
  obtain ⟨C, hC, hb⟩ := exists_unit_caloric_all_radii
  refine ⟨C, hC, ?_⟩
  intro h O hO hKO hh R hR hRone
  let S := localScalarSup (sourceHeat h) (pastBall 0 1)
  by_cases hS : S = ⊤
  · simp only [show localScalarSup (sourceHeat h) (pastBall 0 1) = ⊤ from hS,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC)), add_top, le_top]
  · have hE := unit_pastAffineError_ne_top h O hKO hh.continuousOn
    have hsbound : ∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ S.toReal :=
      fun p hp => localScalarSup_bound _ _ ENNReal.toReal_nonneg
        (by exact (ENNReal.ofReal_toReal hS).ge) hp
    have hbound := hb h O hO hKO hh S.toReal ENNReal.toReal_nonneg hsbound R hR hRone
    have heq : C * ((pastAffineError h 0 1).toReal * R ^ 2 + S.toReal) =
        (C * R ^ 2) * (pastAffineError h 0 1).toReal + C * S.toReal := by ring
    have hmE : ENNReal.ofReal ((C * R ^ 2) * (pastAffineError h 0 1).toReal) =
        ENNReal.ofReal (C * R ^ 2) * pastAffineError h 0 1 := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le (sq_nonneg R)), ENNReal.ofReal_toReal hE]
    have hmS : ENNReal.ofReal (C * S.toReal) = ENNReal.ofReal C * S := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hS]
    rw [heq, ENNReal.ofReal_add (by positivity) (by positivity), hmE, hmS] at hbound
    exact hbound

end GlobalPhi43.Local
