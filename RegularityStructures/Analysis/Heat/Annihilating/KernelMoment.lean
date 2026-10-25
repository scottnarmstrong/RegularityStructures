/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.KernelSupport

/-!
# Moments of the annihilating kernel

`integral_monoFn_mul_annKernel0`: the moments of `annKernel0` of scaled degree `< N` vanish.

Source: [Hai14, Lemma 5.5].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem annKernel0_eq (N : ℕ) (z : ParabolicSpace) :
    annKernel0 N z = heatShell 0 z - annBump N z + scaledShell (annBump N) 1 z := by
  simp [annKernel0, scaledShell]

theorem integral_monoFn_mul_annKernel0 {N : ℕ} (k : PolyIndex N) :
    ∫ z, monoFn k.1 z * annKernel0 N z = 0 := by
  have i1 := integrable_monoFn_mul (contDiff_heatShell 0) (fun z hz => heatShell_eq_zero
    (by simpa using hz)) k.1
  have i2 := integrable_monoFn_mul (contDiff_annBump N) (fun _ hz => annBump_eq_zero hz) k.1
  have i3 : Integrable fun z => monoFn k.1 z * scaledShell (annBump N) 1 z := by
    have h3 := (integrable_monoFn_mul (contDiff_scaledShell (contDiff_annBump N) 1)
      (fun _ hz => scaledShell_eq_zero (fun _ hz => annBump_eq_zero hz) (n := 1)
        (by have : (2 : ℝ)⁻¹ ^ 1 < 1 := by norm_num
            linarith)) k.1)
    exact h3
  have hpt : ∀ z, monoFn k.1 z * annKernel0 N z =
      monoFn k.1 z * heatShell 0 z - monoFn k.1 z * annBump N z +
        monoFn k.1 z * scaledShell (annBump N) 1 z := fun z => by
    rw [annKernel0_eq]; ring
  simp_rw [hpt]
  have e1 := integral_add (i1.sub i2) i3
  have e2 := integral_sub i1 i2
  simp only [Pi.sub_apply] at e1 e2
  rw [e1, e2, integral_monoFn_mul_scaledShell]
  have hμ : ∫ z, monoFn k.1 z * annBump N z = annMoment k := by
    simpa only [evalParabolic_monomial_eq] using integral_monomial_mul_annBump k
  rw [hμ]
  set m := ∫ z, monoFn k.1 z * heatShell 0 z with hm
  have hne : (1 : ℝ) - ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ ≠ 0 := by
    have h1 : (1 : ℝ) < 2 ^ (2 + multiDeg k.1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    have : ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  have hμm : annMoment k * (1 - ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹) = m := by
    unfold annMoment
    simp only [momentMono, evalParabolic_monomial_eq, hm]
    exact div_mul_cancel₀ _ hne
  have he : ((2 : ℝ) ^ 1) ^ 3 * (((2 : ℝ) ^ 1) ^ multiDeg k.1)⁻¹ * (((2 : ℝ) ^ 1) ^ 5)⁻¹ =
      ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ := by
    simp only [pow_one]
    field_simp
    ring
  rw [he]
  linarith

end RegularityStructures

end
