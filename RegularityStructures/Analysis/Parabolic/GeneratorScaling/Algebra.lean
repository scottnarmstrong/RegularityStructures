/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Generator
public import RegularityStructures.Analysis.Parabolic.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Scaling, support and size of the generator on rescaled test functions

For `φ ∈ B^4` and the rescaled `φ^c_z` we show that `L φ^c_z = c⁻⁴ (L φ)^c_z`
(`parabolicGenerator_rescaledTestFunction`), that `L` preserves the support condition, that
`|L φ| ≤ (4π²)⁻¹ + 3 (16π⁴)⁻¹`, and the `L¹` bounds `∫ |φ^c_z| ≤ 16`,
`∫ |L φ^c_z| ≤ 16 (…) c^{-4}`. These supply the test-function hypotheses of
`RegularisingSemigroup.abs_pairing_le` for `φ^c_z` and `L φ^c_z` (order `ℓ = 4`).
-/

public section

namespace RegularityStructures

open MeasureTheory

theorem parabolicDilateCLM_timeDir (c : ℝ) :
    parabolicDilateCLM c timeDir = c ^ 2 • timeDir := by
  simp [parabolicDilate, timeDir]

theorem parabolicDilateCLM_spaceDir (c : ℝ) (i : Fin 3) :
    parabolicDilateCLM c (spaceDir i) = c • spaceDir i := by
  simp [parabolicDilate, spaceDir]

open scoped ContDiff in
/-- Derivative of a rescaled function along a constant direction. -/
theorem iteratedFDeriv_rescaledTestFunction_const {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (c : ℝ) (k : ℕ) (z w v : ParabolicSpace) :
    iteratedFDeriv ℝ k (rescaledTestFunction φ c z) w (fun _ => v) =
      (c ^ 5)⁻¹ * iteratedFDeriv ℝ k φ (parabolicDilate c⁻¹ (w - z))
        (fun _ => parabolicDilateCLM c⁻¹ v) := by
  set D := parabolicDilateCLM c⁻¹ with hD
  have hk : ContDiff ℝ k φ := hφ.of_le (by exact_mod_cast le_top)
  have hψ : ContDiff ℝ k (fun u => φ (u - parabolicDilate c⁻¹ z)) :=
    hk.comp (contDiff_id.sub contDiff_const)
  have hcomp : ContDiff ℝ k ((fun u => φ (u - parabolicDilate c⁻¹ z)) ∘ D) :=
    hψ.comp D.contDiff
  have hDw : D w - parabolicDilate c⁻¹ z = parabolicDilate c⁻¹ (w - z) := by
    simp [hD, parabolicDilate_sub]
  rw [rescaledTestFunction_eq_comp, iteratedFDeriv_const_smul_apply hcomp.contDiffAt,
    D.iteratedFDeriv_comp_right hψ _ le_rfl, iteratedFDeriv_comp_sub, hDw]
  simp

open scoped ContDiff in
/-- Exact scaling of the generator: `L φ^c_z = c⁻⁴ (L φ)^c_z`. -/
theorem parabolicGenerator_rescaledTestFunction {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c) (z w : ParabolicSpace) :
    parabolicGenerator (rescaledTestFunction φ c z) w =
      (c ^ 4)⁻¹ * rescaledTestFunction (parabolicGenerator φ) c z w := by
  have hc' : c ≠ 0 := hc.ne'
  have ht : ∀ f : ParabolicSpace → ℝ, ContDiff ℝ ∞ f → ∀ u : ParabolicSpace,
      iteratedFDeriv ℝ 2 f u (fun _ => parabolicDilateCLM c⁻¹ timeDir) =
        (c ^ 4)⁻¹ * iteratedFDeriv ℝ 2 f u (fun _ => timeDir) := by
    intro f _ u
    rw [parabolicDilateCLM_timeDir]
    have := (iteratedFDeriv ℝ 2 f u).map_smul_univ (fun _ : Fin 2 => (c⁻¹ ^ 2)) (fun _ => timeDir)
    rw [this]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    congr 1
    field_simp
  have hs : ∀ (f : ParabolicSpace → ℝ) (u : ParabolicSpace) (i : Fin 3),
      iteratedFDeriv ℝ 4 f u (fun _ => parabolicDilateCLM c⁻¹ (spaceDir i)) =
        (c ^ 4)⁻¹ * iteratedFDeriv ℝ 4 f u (fun _ => spaceDir i) := by
    intro f u i
    rw [parabolicDilateCLM_spaceDir]
    have := (iteratedFDeriv ℝ 4 f u).map_smul_univ (fun _ : Fin 4 => c⁻¹) (fun _ => spaceDir i)
    rw [this]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    congr 1
    field_simp
  unfold parabolicGenerator
  simp only [iteratedFDeriv_rescaledTestFunction_const hφ, ht _ hφ, hs]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold rescaledTestFunction
  ring

/-- If `φ` vanishes outside the closed unit ball then so does `L φ`. -/
theorem parabolicGenerator_eq_zero {φ : ParabolicSpace → ℝ}
    (hφ : ∀ w, 1 < parabolicNorm w → φ w = 0) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : parabolicGenerator φ w = 0 := by
  have hU : IsOpen {u : ParabolicSpace | 1 < parabolicNorm u} :=
    isOpen_lt continuous_const continuous_parabolicNorm
  have hev : φ =ᶠ[nhds w] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hw) hφ
  have h : ∀ n, iteratedFDeriv ℝ n φ w = iteratedFDeriv ℝ n (fun _ : ParabolicSpace => (0 : ℝ)) w :=
    fun n => (hev.iteratedFDeriv ℝ n).self_of_nhds
  have h0 : ∀ n, iteratedFDeriv ℝ n (fun _ : ParabolicSpace => (0 : ℝ)) w = 0 := fun n => by
    rw [iteratedFDeriv_fun_zero]
    rfl
  unfold parabolicGenerator
  rw [h 2, h 4, h0 2, h0 4]
  simp

/-- The pointwise bound `|L φ| ≤ (4π²)⁻¹ + 3 (16π⁴)⁻¹` on `B^4`. -/
theorem abs_parabolicGenerator_le {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4)
    (w : ParabolicSpace) :
    |parabolicGenerator φ w| ≤ generatorTimeCoeff + 3 * generatorSpaceCoeff := by
  have ht : |iteratedFDeriv ℝ 2 φ w (fun _ => timeDir)| ≤ 1 := by
    have := (iteratedFDeriv ℝ 2 φ w).le_opNorm (fun _ => timeDir)
    simp only [norm_timeDir, Finset.prod_const_one, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (hφ.2.2 2 (by norm_num) w)
  have hs : ∀ i, |iteratedFDeriv ℝ 4 φ w (fun _ => spaceDir i)| ≤ 1 := by
    intro i
    have := (iteratedFDeriv ℝ 4 φ w).le_opNorm (fun _ => spaceDir i)
    simp only [norm_spaceDir, Finset.prod_const_one, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (hφ.2.2 4 le_rfl w)
  have hsum : |∑ i, iteratedFDeriv ℝ 4 φ w (fun _ => spaceDir i)| ≤ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |iteratedFDeriv ℝ 4 φ w (fun _ => spaceDir i)| ≤ ∑ _i : Fin 3, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hs i
      _ = 3 := by simp
  have h1 := generatorTimeCoeff_pos
  have h2 := generatorSpaceCoeff_pos
  unfold parabolicGenerator
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2]
  have a := mul_le_mul_of_nonneg_left ht h1.le
  have b := mul_le_mul_of_nonneg_left hsum h2.le
  linarith

open scoped ContDiff in
theorem continuous_parabolicGenerator {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (parabolicGenerator φ) := by
  have hk : ∀ k : ℕ, ContDiff ℝ k φ := fun k => hφ.of_le (by exact_mod_cast le_top)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := (hk 2).continuous_iteratedFDeriv le_rfl
  have h4 : Continuous (iteratedFDeriv ℝ 4 φ) := (hk 4).continuous_iteratedFDeriv le_rfl
  unfold parabolicGenerator
  refine continuous_const.mul ?_ |>.sub (continuous_const.mul ?_)
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ParabolicSpace) ℝ
      (fun _ => timeDir)).continuous.comp h2
  · refine continuous_finsetSum _ fun i _ => ?_
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => ParabolicSpace) ℝ
      (fun _ => spaceDir i)).continuous.comp h4

end RegularityStructures

end
