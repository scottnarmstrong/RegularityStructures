/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentV
public import Phi43.BPHZ.PositivePiMomentField
public import Phi43.BPHZ.PositivePiMomentSemigroup
public import Phi43.BPHZ.PositiveMomentGammaV
import Mathlib.Tactic

/-!
# Joint measurability and identification of the fields of `I(Ψ²)`, `I(Ψ³)`

* the increment pairing of `Ψ²` is `v₂` and that of the Wick cube is `v₃`
  (`hairerKernelIncrementPairing_psiSq_eq_gammaWickSq`);
* `(ω, y) ↦ v_n(proj x, proj y)(ω)` is jointly measurable on `Ω × ℝ⁴`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The increment pairing of `Ψ²` is `v₂`. -/
theorem hairerKernelIncrementPairing_psiSq_eq_gammaWickSq (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x y : SpaceTime) (ω : Ω) :
    hairerKernelIncrementPairing N x y (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) =
      gammaWickSq N ρ ε ξ x y ω := by
  have hΨ : Continuous (hairerPsiField N ξ ω) := continuous_hairerPsiField N hξ.1 ω
  have hc : Continuous (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
    fun_prop
  have h := hairerKernelIncrementPairing_sub_const_mul N x y
    hc (continuous_const (y := (1 : ℝ))) (hairerWickConstant N ρ ε)
  have h1 : hairerKernelIncrementPairing N x y (fun _ => (1 : ℝ)) = 0 := by
    unfold hairerKernelIncrementPairing
    simpa using integral_hairerI2Psi2Kernel N x y
  rw [h1, mul_zero, sub_zero] at h
  rw [← h]
  unfold gammaWickSq hairerKernelIncrementPairing hairerPsiWickSquare
  simp only [mul_one, sq]

omit [MeasurableSpace Ω] in
/-- The increment pairing of the Wick cube is `v₃`. -/
theorem hairerKernelIncrementPairing_psiCube_eq_gammaWickCube (N : ℕ) (x y : SpaceTime) (ω : Ω) :
    hairerKernelIncrementPairing N x y (hairerTreePsiCube N ξ (hairerWickConstant N ρ ε) ω) =
      gammaWickCube N ρ ε ξ x y ω := rfl

omit [MeasurableSpace Ω] in
/-- The kernel increment `K(proj y - w) - K(x - w)` is jointly measurable in `(y, w)`. -/
theorem measurable_hairerI2Psi2Kernel_proj (N : ℕ) (x : SpaceTime) :
    Measurable fun q : ParabolicSpace × SpaceTime =>
      hairerI2Psi2Kernel N x (spaceTimeProj q.1) q.2 := by
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have h1 : Measurable fun q : ParabolicSpace × SpaceTime => spaceTimeProj q.1 - q.2 :=
    (continuous_spaceTimeProj.measurable.comp measurable_fst).sub measurable_snd
  have h2 : Measurable fun q : ParabolicSpace × SpaceTime => x - q.2 :=
    measurable_const.sub measurable_snd
  exact (hK.comp h1).sub (hK.comp h2)

/-- Joint measurability of `(ω, y) ↦ v₂(x, proj y)(ω)` on `Ω × ℝ⁴`. -/
theorem measurable_gammaWickSq_proj (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    Measurable fun z : Ω × ParabolicSpace => gammaWickSq N ρ ε ξ x (spaceTimeProj z.2) z.1 := by
  have hg : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hg' : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hk : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime =>
      hairerI2Psi2Kernel N x (spaceTimeProj q.1.2) q.2 := by
    have h := (measurable_hairerI2Psi2Kernel_proj N x).comp hg
    exact h
  have hw : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime =>
      hairerPsiWickSquare N ρ ε ξ q.1.1 q.2 := by
    have h := (measurable_hairerPsiWickSquare_uncurry N hξ).comp hg'
    exact h
  have h := ((hk.mul hw).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure SpaceTime))).measurable
  unfold gammaWickSq
  exact h

/-- Joint measurability of `(ω, y) ↦ v₃(x, proj y)(ω)` on `Ω × ℝ⁴`. -/
theorem measurable_gammaWickCube_proj (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    Measurable fun z : Ω × ParabolicSpace => gammaWickCube N ρ ε ξ x (spaceTimeProj z.2) z.1 := by
  have hg : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hg' : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hk : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime =>
      hairerI2Psi2Kernel N x (spaceTimeProj q.1.2) q.2 := by
    have h := (measurable_hairerI2Psi2Kernel_proj N x).comp hg
    exact h
  have hw : Measurable fun q : (Ω × ParabolicSpace) × SpaceTime =>
      hairerPsiWickCube N ρ ε ξ q.1.1 q.2 := by
    have h := (measurable_hairerPsiWickCube_uncurry N hξ).comp hg'
    exact h
  have h := ((hk.mul hw).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure SpaceTime))).measurable
  unfold gammaWickCube
  exact h

end RegularityStructures.Phi43

end
